import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey
/-!
# Erdős Problem 556

A problem of Bondy and Erdős: for the cycle $C_n$ with $n \ge 4$, the $3$-colour Ramsey number
satisfies
$$R(C_n; 3) \le 4n - 3.$$
The triangle is excluded: $C_3 = K_3$ and $R(K_3; 3) = 17 > 9$ [Rad]. The bound is best possible for odd $n$, where equality is conjectured (and known for large odd
$n$). Łuczak proved the asymptotic bound $R(C_n; 3) \le (4 + o(1))n$, and $(3 + o(1))n$ for even
$n$; Kohayakawa, Simonovits and Skokan settled large odd $n$, and Benevides and Skokan large even
$n$, but the inequality for all $n$ remains open.

*References:*
- [erdosproblems.com/556](https://www.erdosproblems.com/556)
- [Er81] P. Erdős, *On the combinatorial problems which I would most like to see solved*,
  Combinatorica 1 (1981), 25-42.
- [Lu99] T. Łuczak, *$R(C_n, C_n, C_n) \le (4 + o(1))n$*, J. Combin. Theory Ser. B 75 (1999),
  174-187.
- [KSS05] Y. Kohayakawa, M. Simonovits, J. Skokan, *The 3-colored Ramsey number of odd cycles*,
  Proceedings of GRACO2005 (2005), 397-402.
- [BeSk09] F. S. Benevides, J. Skokan, *The 3-colored Ramsey number of even cycles*, J. Combin.
  Theory Ser. B 99 (2009), 690-708.
- [Rad] S. P. Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1,
  revision 18, [p. 61](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/#page=61).
-/

section

open Filter

namespace Erdos556

open SimpleGraph

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 3)) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n > 3) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 4) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (n ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : n ≥ 3) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 > 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 > 4 * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 < n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≥ 4 * n - 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 < multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 < multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hodd : Odd n) :
    (3 ≤ n) ↔ (2 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (5 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n), 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) →
    (∀ (n : ℕ) (hn : 2 < n) (hodd : Odd n), 4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (Odd n) ∧ (¬(4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3) ↔ (4 * n - 3 ≥ multicolourRamsey (cycleGraph n) 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
