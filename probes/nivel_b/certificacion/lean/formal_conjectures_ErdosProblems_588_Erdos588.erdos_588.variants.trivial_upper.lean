import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.2d
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 588

*References:*
- [erdosproblems.com/588](https://www.erdosproblems.com/588)
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [Er84] Erdős, P., *Research problems*. Period. Math. Hungar. (1984), 101-103.
- [FuPa84] Füredi, Z. and Palásti, I., *Arrangements of lines with a large number of
  triangles*. Proc. Amer. Math. Soc. (1984), 561-566.
- [Gr76] Grünbaum, Branko, *New views on some old questions of combinatorial geometry*.
  Colloquio Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo I (1976), 451-468.
- [Ka63] Kárteszi, F., *Sylvester egy tételéről és Erdős egy sejtéséről*. Matematikai Lapok
  (1963), 3-10.
- [SoSt13] Solymosi, József and Stojaković, Miloš, *Many collinear $k$-tuples with no $k+1$
  collinear points*. Discrete Comput. Geom. (2013), 811-820.
-/

section

open EuclideanGeometry Filter Asymptotics

namespace Erdos588

/--
`numLinesWithPointsMax k n` is $f_k(n)$: the maximum number of lines containing exactly $k$
points among all sets $S$ of $n$ points in $\mathbb{R}^2$ with no $k + 1$ points on a line.

Since $S$ has no $k + 1$ points on a line, the lines with at least $k$ points of $S$ are exactly
the lines with exactly $k$ points of $S$. The definition follows Erdős Problem 101 (the case
$k = 4$).
-/
noncomputable def numLinesWithPointsMax (k n : ℕ) : ℕ :=
  sSup {((linesWithPointsFor k S).ncard) | (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor (k + 1) S)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk₀ : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk₀ : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk₀ : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk₀ : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk₀ : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : ¬(k < 2)), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : ¬(k < 2)), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : ¬(k < 2)), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : ¬(k < 2)), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : ¬(k < 2)), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k > 2), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 3), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : k ≥ 2), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) > numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 < k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 3 ≤ k), n * (n - 1) ≥ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (n * (n - 1) ≤ numLinesWithPointsMax k n * (k * (k - 1)))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) < n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 2 ≤ k), numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) →
    (∀ (k n : ℕ) (hk : 1 < k), numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), (2 ≤ k) ∧ (¬(numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (n : ℕ), ¬((numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1)) ↔ (numLinesWithPointsMax k n * (k * (k - 1)) ≥ n * (n - 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k n : ℕ) (hk : 2 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k n : ℕ) (hk : 2 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (hk : 2 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k n : ℕ) (hk : 2 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (hk : 2 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
