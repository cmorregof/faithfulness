import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.RingTheory.Valuation.LocalUniformization
/-!
# Local uniformization

Let $F$ be a finitely generated field extension of a field $k$ and let $\mathcal{O}$ be a
valuation ring of $F$ containing $k$. *Local uniformization* asks for an affine model of
$F \mid k$ on which the centre of $\mathcal{O}$ is a regular point: a finitely generated
$k$-subalgebra $A \subseteq \mathcal{O}$ with fraction field $F$ such that $A_\mathfrak{p}$ is
regular, where $\mathfrak{p} = \mathfrak{m}_\mathcal{O} \cap A$ is the centre.

This is the local form of resolution of singularities, one valuation at a time. Zariski
introduced it and proved it in characteristic zero, and deduced resolution of singularities in
dimension at most three from it. In positive characteristic it is known in dimension at most
three, and open from dimension four on. A place is *Abhyankar* when the rational rank of its
value group and the transcendence degree of its residue field over $k$ add up to the
transcendence degree of $F \mid k$; an Abhyankar place whose residue field is separable over $k$
is uniformized in any dimension [KK2005].

The form asked here is the weak one: some affine model of $F \mid k$ works. The proofs give the
strong form, where the model may moreover be required to contain a prescribed finite subset of
$\mathcal{O}$, and that is the form that patches into a resolution of singularities.

The conclusion here asks that the centre be a regular point, not a smooth one. Over a perfect
field the two agree; over an imperfect field regularity is the right condition, since already
$k(a^{1/p}) \mid k$ for $a \in k \setminus k^p$ has no model that is smooth over $k$.

For a field extension, `Algebra.EssFiniteType k F` says that $F$ is finitely generated as a
field over $k$, and `Algebra.trdeg k F` is the transcendence degree, the dimension of a model.
The centre `ValuationSubring.centerOn` and the predicate `ValuationSubring.HasLocalUniformization`
are defined in `FormalConjecturesForMathlib.RingTheory.Valuation.LocalUniformization`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Local_uniformization)
- [Zar1940] O. Zariski, [Local uniformization on algebraic
  varieties](https://doi.org/10.2307/1968864), Ann. of Math. 41 (1940), 852--896.
- [Abh1956] S. Abhyankar, [Local uniformization on algebraic surfaces over ground fields of
  characteristic $p \neq 0$](https://doi.org/10.2307/1970014), Ann. of Math. 63 (1956), 491--526.
- [Abh1966] S. Abhyankar, Resolution of singularities of embedded algebraic surfaces, Monographs
  in Pure and Applied Mathematics 24, Academic Press, 1966; birational resolution of threefolds
  over an algebraically closed field of characteristic $p > 5$.
- [Cut2009] S. D. Cutkosky, [Resolution of singularities for 3-folds in positive
  characteristic](https://doi.org/10.1353/ajm.0.0036), Amer. J. Math. 131 (2009), 59--127; a
  simplification of [Abh1966], also over an algebraically closed field.
- [CP2008] V. Cossart and O. Piltant, [Resolution of singularities of threefolds in positive
  characteristic I](https://doi.org/10.1016/j.jalgebra.2008.03.032), J. Algebra 320 (2008),
  1051--1082.
- [CP2009] V. Cossart and O. Piltant, [Resolution of singularities of threefolds in positive
  characteristic II](https://doi.org/10.1016/j.jalgebra.2008.11.030), J. Algebra 321 (2009),
  1836--1976; quasi-projective threefolds over a field $k$ with $[k : k^p] < \infty$, in every
  positive characteristic.
- [CP2019] V. Cossart and O. Piltant, [Resolution of singularities of arithmetical
  threefolds](https://doi.org/10.1016/j.jalgebra.2019.02.017), J. Algebra 529 (2019), 268--535.
- [KK2005] H. Knaf and F.-V. Kuhlmann, [Abhyankar places admit local uniformization in any
  characteristic](https://doi.org/10.1016/j.ansens.2005.09.001), Ann. Sci. École Norm. Sup. 38
  (2005), 833--846; the hypotheses are that the place is Abhyankar and that its residue field is
  separable over the ground field.
- [KK2009] H. Knaf and F.-V. Kuhlmann, [Every place admits local uniformization in a finite
  extension of the function field](https://doi.org/10.1016/j.aim.2008.12.009), Adv. Math. 221
  (2009), 428--453.
- [Tem2013] M. Temkin, [Inseparable local
  uniformization](https://doi.org/10.1016/j.jalgebra.2012.09.023), J. Algebra 373 (2013), 65--119.
-/

section

open IsLocalRing ValuationSubring

namespace LocalUniformization

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22 u_c23 u_c24 u_c25 u_c26 u_c27 u_c28
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c2) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c1) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c3) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c4) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c5) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F < 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c6) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F < 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c8) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 4), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c7) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c9) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (Algebra.trdeg k F ≤ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c10) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c11) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c12) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 ≥ Algebra.trdeg k F) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c10) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c11) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c10) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c11) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c10) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c11) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c10) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c11) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c13) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c14) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hF : Algebra.trdeg k F ≤ 3) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c13) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c14) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hF : Algebra.trdeg k F ≤ 3) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c13) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c14) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hF : Algebra.trdeg k F ≤ 3) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c13) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c14) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hF : Algebra.trdeg k F ≤ 3) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c13) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c14) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hF : Algebra.trdeg k F ≤ 3) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c16) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c17) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk₀ : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c16) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c17) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk₀ : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c16) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c17) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk₀ : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c16) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c17) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk₀ : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c16) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) ↔
    (∀ (k F : Type u_c17) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk₀ : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c19) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c20) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 3 > Algebra.trdeg k F), 𝒪.HasLocalUniformization k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c21) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (3 > Algebra.trdeg k F) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c23) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : 4 ≥ Algebra.trdeg k F), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c22) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c24) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (4 ≥ Algebra.trdeg k F) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k F : Type u_c26) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪), 𝒪.HasLocalUniformization k) →
    (∀ (k F : Type u_c25) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3), 𝒪.HasLocalUniformization k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c27) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    (Algebra.trdeg k F ≤ 3) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example (k F : Type u_c28) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k F : Type u_c28) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k F : Type u_c28) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k F : Type u_c28) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k F : Type u_c28) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) (hF : Algebra.trdeg k F ≤ 3) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
