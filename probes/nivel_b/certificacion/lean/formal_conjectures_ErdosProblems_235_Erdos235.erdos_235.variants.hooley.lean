import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 235

*References:*
- [erdosproblems.com/235](https://www.erdosproblems.com/235)
- [Ho65] Hooley, Christopher, _On the difference between consecutive numbers prime to $n$_. II.
  Publ. Math. Debrecen (1965), 39--49.
-/

section

open Filter
open scoped Topology

namespace Erdos235

/-- The product of the first `k + 1` primes.
On [erdosproblems.com/235](https://www.erdosproblems.com/235) this is $N_{k+1}=2\cdot 3\cdots p_{k+1}$.
The limit as $k\to\infty$ is the same for either indexing. -/
noncomputable def N (k : ℕ) : ℕ :=
  primorial (Nat.nth Nat.Prime k)

/-- The increasing list of integers `< n` that are coprime to `n`. -/
def coprimeList (n : ℕ) : List ℕ :=
  ({a ∈ Finset.range n | n.Coprime a}).sort (· ≤ ·)

/-- The gaps $a_i - a_{i-1}$ between consecutive entries of `coprimeList n`. -/
def gaps (n : ℕ) : List ℕ :=
  (coprimeList n).zipWith (fun a b ↦ b - a) (coprimeList n).tail

/-- The number of gaps of size at most $c \cdot n / \varphi(n)$. -/
noncomputable def countGaps (n : ℕ) (c : ℝ) : ℕ :=
  (gaps n).countP fun g ↦ decide ((g : ℝ) ≤ c * (n : ℝ) / (n.totient : ℝ))

/-- The proportion appearing in `erdos_235`, for the primorial `N k`. -/
noncomputable def proportion (k : ℕ) (c : ℝ) : ℝ :=
  (countGaps (N k) c : ℝ) / ((N k).totient : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : 0 < c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  simp_all

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (0 < c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (0 < c))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (0 < c))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (0 < c))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (0 < c))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (0 < c))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (0 < c))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (0 < c)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (0 < c)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (0 < c)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (0 < c)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (0 < c)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (0 < c)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : c ≥ 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (c ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : c ≥ 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : c ≥ 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : c ≥ 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : c ≥ 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc₀ : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc₀ : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc₀ : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc₀ : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc₀ : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : ¬(c < 0)), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 ≤ c) ↔ (¬(c < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : ¬(c < 0)), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : ¬(c < 0)), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : ¬(c < 0)), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) ↔
    (∀ (c : ℝ) (hc : ¬(c < 0)), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) →
    (∀ (c : ℝ) (hc : c > 0), Tendsto (fun k ↦ proportion k c) atTop (𝓝 (1 - Real.exp (-c)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 ≤ c) ↔ (c > 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (c > 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (c > 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (c > 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (c > 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (c > 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 ≤ c) ↔ (c > 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (c > 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (c > 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (c > 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (c > 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (c > 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 ≤ c) ↔ (c > 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 ≤ c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 ≤ c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 ≤ c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 ≤ c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 ≤ c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
