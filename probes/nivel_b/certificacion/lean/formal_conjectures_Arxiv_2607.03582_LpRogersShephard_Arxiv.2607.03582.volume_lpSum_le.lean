import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Planar $L_p$-Rogers-Shephard, the equality case

*Reference:* [arxiv/2607.03582](https://arxiv.org/abs/2607.03582)
**$L_p$-Rogers-Shephard type inequalities for $L_p$-zonoids and symmetric bodies**
by *Matthieu Fradelizi, Auttawich Manui, Mark Meyer, Cheikh Saliou Ndiaye*

*Formal proof of Conjecture 5:* Kenta Kitamura,
[Lean proofs for the symmetric L_p Rogers–Shephard conjectures](https://github.com/KitaKen1/lp-rogers-shephard-conjectures-lean/tree/c646c668c0568b8533bf5534abcf02aab4d2df72).

Corollary 29 bounds $|K \oplus_p -K|$ against $|K|$ for planar convex bodies with a centre of
symmetry containing the origin, and notes that parallelograms with a vertex at the origin
attain it. Conjecture 5 asks whether they are the only bodies that do.
-/

section

open MeasureTheory Real

open scoped EuclideanGeometry

namespace Arxiv.«2607.03582»

/-- The support function $h_K(u) = \sup_{x \in K} \langle x, u\rangle$. -/
noncomputable def supportFunction (K : Set ℝ²) (u : ℝ²) : ℝ := ⨆ x : K, inner ℝ (x : ℝ²) u

/-- The Firey $L_p$-sum $K \oplus_p L$, equation (4) of the source: the body whose support
function is $(h_K^p + h_L^p)^{1/p}$.

The source defines it by that support function, which needs both bodies to contain the origin.
Here it is the intersection of the halfspaces the support function cuts out, which agrees with
the source's set on the bodies the statements below quantify over and needs no separate
existence argument. -/
noncomputable def lpSum (p : ℝ) (K L : Set ℝ²) : Set ℝ² :=
  {x | ∀ u : ℝ², inner ℝ x u ≤ (supportFunction K u ^ p + supportFunction L u ^ p) ^ (1 / p)}

/-- $K$ has a centre of symmetry: some $c$ with $K$ invariant under reflection in $c$. -/
def HasCentreOfSymmetry (K : Set ℝ²) : Prop := ∃ c : ℝ², ∀ x, x ∈ K ↔ (2 • c - x) ∈ K

/-- The constant of Corollary 29, $\frac{2\Gamma(1+1/q)^2}{\Gamma(1+2/q)} + 2$. -/
noncomputable def rsConstant (q : ℝ) : ℝ :=
  2 * Real.Gamma (1 + 1 / q) ^ 2 / Real.Gamma (1 + 2 / q) + 2

/-- $K$ is a parallelogram with a vertex at the origin: the convex hull of $0$, $a$, $b$ and
$a + b$ for linearly independent $a$, $b$. -/
def IsParallelogramAtOrigin (K : Set ℝ²) : Prop :=
  ∃ a b : ℝ², LinearIndependent ℝ ![a, b] ∧ K = convexHull ℝ {0, a, b, a + b}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (p > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔ (ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK₀ : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK₀ : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK₀ : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK₀ : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK₀ : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : ¬(p ≤ 1)) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) :
    (1 < p) ↔ (¬(p ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : ¬(p ≤ 1)) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : ¬(p ≤ 1)) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : ¬(p ≤ 1)) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) ↔
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : ¬(p ≤ 1)) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) < ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p ≥ 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (p ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (p ≥ 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (p ≥ 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (p ≥ 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (p ≥ 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (p ≥ 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (p ≥ 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : p > 1) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≥ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K > volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 ≤ p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≥ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (1 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (1 ≤ p)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), ENNReal.ofReal (rsConstant q) * volume K ≤ volume (lpSum p K (-K))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (K : Set ℝ²) (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) →
    (∀ (K : Set ℝ²) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (p q : ℝ) (hp : 1 < p) (hq : 1 / p + 1 / q = 1), volume (lpSum p K (-K)) ≤ ENNReal.ofReal (rsConstant q) * volume K) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hq : 1 / p + 1 / q = 1) :
    (1 < p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((1 < p) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (K : Set ℝ²) (p q : ℝ) (hK : Convex ℝ K) (hKc : IsCompact K) (hKi : (interior K).Nonempty) (hsym : HasCentreOfSymmetry K) (h0 : (0 : ℝ²) ∈ K) (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
