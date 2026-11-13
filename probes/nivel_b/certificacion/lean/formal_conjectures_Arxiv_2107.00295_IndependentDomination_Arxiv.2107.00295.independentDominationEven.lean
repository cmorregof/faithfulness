import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
/-!
# Independent Domination of Regular Graphs, Conjecture 1.6

*Reference:* [arxiv/2107.00295](https://arxiv.org/abs/2107.00295)
**On independent domination of regular graphs**
by *Eun-Kyung Cho, Ilkyoo Choi, Boram Park*

The conjecture was subsequently proved by Cho, Kim, Kim and Oum, as
Corollary 1.3 of:

*Reference:* [arxiv/2202.09594](https://arxiv.org/abs/2202.09594)
**Independent domination of graphs with bounded maximum degree**
by *Eun-Kyung Cho, Jinha Kim, Minki Kim, Sang-il Oum*,
J. Combin. Theory Ser. B 158 (2023), 341-352.

Corollary 1.3 states that every graph $G$ with maximum degree at most $\Delta$
and no isolated vertices has an independent dominating set of size at most
$\left(1 - \frac{\Delta}{\lfloor (\Delta+2)^2/4 \rfloor}\right)\lvert V(G)\rvert$.
Expanding the floor for even and odd $\Delta$ gives exactly the two
statements below.
-/

section
namespace Arxiv.«2107.00295»
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (0 < G.minDegree) ∧ (Even G.maxDegree) ∧ (¬(let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (0 < G.minDegree) ∧ (Even G.maxDegree) ∧ (¬(let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔ (let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔ (let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (G.minDegree > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hEven : Even G.maxDegree) (hIso : 0 < G.minDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hEven : Even G.maxDegree) (hIso : 0 < G.minDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hEven : Even G.maxDegree) (hIso : 0 < G.minDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hEven : Even G.maxDegree) (hIso : 0 < G.minDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hEven : Even G.maxDegree) (hIso : 0 < G.minDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso₀ : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso₀ : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso₀ : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso₀ : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso₀ : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : ¬(G.minDegree ≤ 0)) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (0 < G.minDegree) ↔ (¬(G.minDegree ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : ¬(G.minDegree ≤ 0)) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : ¬(G.minDegree ≤ 0)) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : ¬(G.minDegree ≤ 0)) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔
    (∀ (hIso : ¬(G.minDegree ≤ 0)) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) →
    (∀ (hIso : G.minDegree > 0) (hEven : Even G.maxDegree), let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (0 < G.minDegree) ∧ (Even G.maxDegree) ∧ (¬(let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (0 < G.minDegree) ∧ (Even G.maxDegree) ∧ (¬(let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔ (let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 2)^2 * i ≤ (D^2 + 4) * n) ↔ (let D := G.maxDegree
    let i := G.indepDominationNumber
    let n := Fintype.card V
    (D + 3)^2 * i ≤ (D^2 + 4) * n)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hIso : 0 < G.minDegree) (hEven : Even G.maxDegree) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
