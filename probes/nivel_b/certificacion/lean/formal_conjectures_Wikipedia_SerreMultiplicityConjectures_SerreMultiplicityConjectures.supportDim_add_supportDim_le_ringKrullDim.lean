import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Serre's multiplicity conjectures

Let $R$ be a regular local ring and let $M$, $N$ be finitely generated $R$-modules such that
$M \otimes_R N$ has finite length. Serre defined the intersection multiplicity
$$\chi(M, N) = \sum_{i \ge 0} (-1)^i \ell_R(\operatorname{Tor}_i^R(M, N)).$$
He proved the dimension inequality $\dim M + \dim N \le \dim R$ for every regular local ring,
and conjectured the following three properties:

- **Non-negativity:** $\chi(M, N) \ge 0$.
- **Vanishing:** if $\dim M + \dim N < \dim R$, then $\chi(M, N) = 0$.
- **Positivity:** if $\dim M + \dim N = \dim R$, then $\chi(M, N) > 0$.

Serre proved all three when $R$ is of equal characteristic, or of mixed characteristic and
unramified. Vanishing was proved in general by Roberts and, independently, by Gillet and Soulé.
Non-negativity was proved in general by Gabber. Positivity is open in general. For Serre's two
special cases, this file states only positivity, since non-negativity and vanishing are now known
in general.

The intersection multiplicity is `Module.intersectionMultiplicity`, defined in
`FormalConjecturesForMathlib.RingTheory.IntersectionMultiplicity`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Serre%27s_multiplicity_conjectures)
- [Se00] J.-P. Serre, *Local algebra*, Springer Monographs in Mathematics, Springer, 2000,
  Chapter V, Part B.
- [Ro85] P. Roberts, *The vanishing of intersection multiplicities of perfect complexes*,
  Bull. Amer. Math. Soc. 13 (1985), 127–130.
- [GS87] H. Gillet, C. Soulé, *Intersection theory using Adams operations*,
  Invent. Math. 90 (1987), 243–277.
- [Ro98] P. Roberts, *Recent developments on Serre's multiplicity conjectures: Gabber's proof of
  the nonnegativity conjecture*, Enseign. Math. 44 (1998), 305–324.
- [Sk19] C. Skalit, *Positivity of intersection multiplicity over a two-dimensional base*,
  J. Pure Appl. Algebra 223 (2019), 1801–1816.
  [arXiv:1510.05146](https://arxiv.org/abs/1510.05146)
-/

section

open IsLocalRing Module TensorProduct

namespace SerreMultiplicityConjectures

universe u

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]
  (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N < ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(Module.supportDim R M + Module.supportDim R N < ringKrullDim R)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(Module.supportDim R M + Module.supportDim R N < ringKrullDim R)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (Module.supportDim R M + Module.supportDim R N < ringKrullDim R)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (Module.supportDim R M + Module.supportDim R N < ringKrullDim R)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (Module.supportDim R M + Module.supportDim R N ≥ ringKrullDim R)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≥ Module.supportDim R M + Module.supportDim R N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h₀ : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h₀ : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h₀ : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h₀ : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔
    (∀ (h₀ : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R > Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(ringKrullDim R > Module.supportDim R M + Module.supportDim R N)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(ringKrullDim R > Module.supportDim R M + Module.supportDim R N)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R > Module.supportDim R M + Module.supportDim R N)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R > Module.supportDim R M + Module.supportDim R N)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) →
    (∀ (h : IsFiniteLength R (M ⊗[R] N)), ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (IsFiniteLength R (M ⊗[R] N)) ∧ (¬(ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R) ↔ (ringKrullDim R ≤ Module.supportDim R M + Module.supportDim R N)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (h : IsFiniteLength R (M ⊗[R] N)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (h : IsFiniteLength R (M ⊗[R] N)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (h : IsFiniteLength R (M ⊗[R] N)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (h : IsFiniteLength R (M ⊗[R] N)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h : IsFiniteLength R (M ⊗[R] N)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
