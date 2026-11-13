import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 781

*References:*
- [erdosproblems.com/781](https://www.erdosproblems.com/781)
- [BEF90] Brown, T. C. and Erdős, P. and Freedman, A. R., _Quasi-progressions and descending
  waves_. J. Combin. Theory Ser. A (1990), 81-95.
- [AlSp89] Alon, N. and Spencer, Joel, _Ascending waves_. J. Combin. Theory Ser. A (1989),
  275-287.
-/

section

open Filter Asymptotics

namespace Erdos781

/-- A $k$-term *descending wave* is a sequence $x_1<\cdots <x_k$ such that, for $1<j<k$,
$x_j \geq \frac{x_{j+1}+x_{j-1}}{2}$. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧
    ∀ i j l : Fin k, (i : ℕ) + 1 = j → (j : ℕ) + 1 = l → x i + x l ≤ 2 * x j

/-- `f k` is the minimal `n` such that any $2$-colouring of $\{1,\ldots,n\}$ (identified with
`Fin n`) contains a monochromatic $k$-term descending wave. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | ∀ c : Fin n → Fin 2, ∃ x : Fin k → Fin n,
    IsDescendingWave (fun i ↦ (x i : ℕ)) ∧ ∃ γ, ∀ i, c (x i) = γ}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3 ∧ k ^ 2 - k + 1 ≤ f k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 1)), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k > 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : k ≥ 1), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 0 < k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ (k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 5 * k + 9) / 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) →
    (∀ (k : ℕ) (hk : 1 ≤ k), (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ^ 2 - k + 1 ≤ f k ∧ (f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3) ↔ ((f k : ℚ) ≤ (k ^ 3 - 4 * k + 9) / 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 1 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 1 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 1 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 1 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 1 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
