import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 408

*References:*
- [erdosproblems.com/408](https://www.erdosproblems.com/408)
- [OEIS A003434](https://oeis.org/A003434): the values $f(n)$ for $n \geq 2$.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathématique (1980).
- [Pi29] Pillai, S. Sivasankaranarayana, *On a function connected with $\phi(n)$*. Bull. Amer.
  Math. Soc. 35 (1929), 837-841.
  [doi:10.1090/S0002-9904-1929-04800-6](https://doi.org/10.1090/S0002-9904-1929-04800-6)
- [Sh50] Shapiro, Harold N., *On the iterates of a certain class of arithmetic functions*. Comm.
  Pure Appl. Math. 3 (1950), 259-272.
- [EGPS90] Erdős, P., Granville, A., Pomerance, C. and Spiro, C., *On the normal behavior of the
  iterates of some arithmetic functions*. Analytic number theory (Allerton Park, IL, 1989),
  Progr. Math. 85 (1990), 165-204.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. Third edition, Springer (2004),
  Problem B41.
- [FKL10] Ford, K., Konyagin, S. V. and Luca, F., *Prime chains and Pratt trees*. Geom. Funct.
  Anal. 20 (2010), 1231-1258. [arXiv:0904.0473](https://arxiv.org/abs/0904.0473)
  [doi:10.1007/s00039-010-0089-0](https://doi.org/10.1007/s00039-010-0089-0)
-/

section

open Filter
open scoped Topology

namespace Erdos408

/--
`f n` is $f(n) = \min\{k \geq 1 : \phi_k(n) = 1\}$, where $\phi_1 = \phi$ is Euler's totient
function and $\phi_k(n) = \phi(\phi_{k-1}(n))$. As in the source, $k$ starts at $1$, so
$f(1) = 1$. Every iterate of $\phi$ at $0$ is $0$, so `sInf ∅ = 0` gives the junk value
$f(0) = 0$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 < k), f (2 ^ k) = k) := by
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
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (3 ^ k) = k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1), f (2 ^ k) = k

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
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), f (2 ^ k) = k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), f (2 ^ k) = k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), f (2 ^ k) = k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : k ≥ 1), f (2 ^ k) = k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), f (2 ^ k) = k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), f (2 ^ k) = k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), f (2 ^ k) = k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k), f (2 ^ k) = k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 1)), f (2 ^ k) = k

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
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), f (2 ^ k) = k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), f (2 ^ k) = k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), f (2 ^ k) = k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)), f (2 ^ k) = k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), f (2 ^ k) = k

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
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : 0 < k), f (2 ^ k) = k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : 0 < k), f (2 ^ k) = k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : 0 < k), f (2 ^ k) = k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) ↔
    (∀ (k : ℕ) (hk : 0 < k), f (2 ^ k) = k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k > 1), f (2 ^ k) = k) := by
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
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : k ≥ 1), f (3 ^ k) = k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) →
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), f (2 ^ k) = k) →
    (∀ (k : ℕ) (hk : 0 < k), f (3 ^ k) = k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (1 ≤ k) ∧ (¬(f (3 ^ k) = k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((f (2 ^ k) = k) ↔ (f (3 ^ k) = k)) :=
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
