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
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (0 ≤ ε) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : ε > 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ε > 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ε > 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ε > 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ε > 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔ (∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k₁ : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k₁] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hδ : 0 < δ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε₀ : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε₀ : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε₀ : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε₀ : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε₀ : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : ¬(ε ≤ 0)) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ¬(ε ≤ 0)) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ¬(ε ≤ 0)) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ¬(ε ≤ 0)) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) ↔
    (∀ (ε δ : ℝ) (hε : ¬(ε ≤ 0)) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : ε ≥ 0) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hδ : 0 < δ) :
    (0 < ε) ↔ (ε ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < δ) ∧ (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε δ : ℝ) (hε : 0 < ε), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) →
    (∀ (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ), ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) :
    (0 < δ) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ) (δ : ℝ), (0 < ε) ∧ (¬((0 < δ) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((0 < δ) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((0 < δ) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((0 < δ) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((0 < δ) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((0 < δ) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (δ : ℝ), ¬((0 < δ) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
