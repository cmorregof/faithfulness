import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
/-!
# Vizing's conjecture (1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Vizing%27s_conjecture)
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [ClSu00] Clark, W. E. and Suen, S. (2000). "An inequality related to Vizing's conjecture."
  *Electron. J. Combin.* 7, N4.
* [SuTa12] Suen, S. and Tarr, J. (2012). "An improved inequality related to Vizing's conjecture."
  *Electron. J. Combin.* 19, P8.
* [BDGHHKR12] Brešar, B., Dorbec, P., Goddard, W., Hartnell, B. L., Henning, M. A., Klavžar, S.
  and Rall, D. F. (2012). "Vizing's conjecture: a survey and recent results."
  *J. Graph Theory* 69, pp. 46--76.
-/

section

open SimpleGraph

namespace VizingConjecture

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber < 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 3 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≥ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) :
    (G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔ (2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H₀ : SimpleGraph β), G.dominationNumber * H₀.dominationNumber ≤ 2 * (G □ H₀).dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H₀ : SimpleGraph β), G.dominationNumber * H₀.dominationNumber ≤ 2 * (G □ H₀).dominationNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H₀ : SimpleGraph β), G.dominationNumber * H₀.dominationNumber ≤ 2 * (G □ H₀).dominationNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H₀ : SimpleGraph β), G.dominationNumber * H₀.dominationNumber ≤ 2 * (G □ H₀).dominationNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) ↔
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H₀ : SimpleGraph β), G.dominationNumber * H₀.dominationNumber ≤ 2 * (G □ H₀).dominationNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber > G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 3 * (G □ H).dominationNumber ≥ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber) →
    (∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β), 2 * (G □ H).dominationNumber ≤ G.dominationNumber * H.dominationNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
