import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Open Quantum Problem 35: existence of absolutely maximally entangled pure states

**Problem:** For which numbers of parties $n$ and local dimensions $d$ does there
exist a pure absolutely maximally entangled state $\psi$?

A pure state $\psi$ on $n$ parties of local dimension $d$ is called
**absolutely maximally entangled (AME)** if, for every subset of at most half
of the parties, the corresponding reduced density matrix is maximally mixed.

*References:*
- Open Quantum Problems, Problem 35:
  <https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states>
- Formal Conjectures issue #3452:
  <https://github.com/google-deepmind/formal-conjectures/issues/3452>
- W. Helwig, W. Cui, A. Riera, J. I. Latorre, and H.-K. Lo,
  *Absolute Maximal Entanglement and Quantum Secret Sharing*,
  Phys. Rev. A 86, 052335 (2012), arXiv:1204.2289.
- D. Goyeneche, D. Alsina, J. I. Latorre, A. Riera, and K. Życzkowski,
  *Absolutely Maximally Entangled states, combinatorial designs and multi-unitary matrices*,
  Phys. Rev. A 92, 032316 (2015), arXiv:1506.08857.
- A. Higuchi and A. Sudbery,
  *How entangled can two couples get?*,
  Phys. Lett. A 273, 213-217 (2000), arXiv:quant-ph/0005013.
- A. J. Scott,
  *Multipartite entanglement, quantum-error-correcting codes, and entangling power of quantum
  evolutions*, Phys. Rev. A 69, 052330 (2004), arXiv:quant-ph/0310137.
- F. Huber, O. Gühne, and J. Siewert,
  *Absolutely maximally entangled states of seven qubits do not exist*,
  Phys. Rev. Lett. 118, 200502 (2017), arXiv:1608.06228.
- F. Huber and M. Grassl,
  *Quantum Codes of Maximal Distance and Highly Entangled Subspaces*,
  Quantum 4, 284 (2020), arXiv:1907.07733.
- S. A. Rather, A. Burchardt, W. Bruzda, G. Rajchel-Mieldzioć,
  A. Lakshminarayan, and K. Życzkowski,
  *Thirty-six entangled officers of Euler: Quantum solution to a classically impossible problem*,
  Phys. Rev. Lett. 128, 080507 (2022), arXiv:2104.05122.
- G. Rajchel-Mieldzioć, R. Bistroń, A. Rico, A. Lakshminarayan,
  and K. Życzkowski,
  *Absolutely maximally entangled pure states of multipartite quantum systems*,
  arXiv:2508.04777 (2025).
- S. Bevins and Y. Bidav,
  *Symmetry-guided constructions of absolutely maximally entangled states in five open cases*,
  [arXiv:2608.05781](https://arxiv.org/abs/2608.05781) (2026).
- F. Shi, X. Zhang, Q. Zhao, and L. Li,
  *Complete Existence Classification of Seven-Partite Absolutely Maximally Entangled States*,
  [arXiv:2608.01011](https://arxiv.org/abs/2608.01011) (2026).

This file formalizes the problem of determining for which pairs $(n,d)$ there exists an
absolutely maximally entangled pure state $\mathrm{AME}(n,d)$.

We represent an $n$-partite state of local dimension $d$ by the finite-dimensional Hilbert space
`EuclideanSpace ℂ (Config n d)`, whose coordinates in the computational basis are amplitudes.
The helper `mkStateVector` turns an amplitude function into such a state, and normalization is
imposed explicitly via `IsNormalized`, i.e. via the ambient $L^2$ norm.

The main reusable lemma is `reducedDensityFirst_of_completion`: if a state is a
uniform superposition over the graph of an injective completion function
`completion : Config m d → Config (n - m) d`,
then the reduced state on the first $m$ parties is maximally mixed.

As demonstration, we show that the Bell states with $n=2$ and GHZ states with $n=3$ are
AME states, and the GHZ state with $n=4$ is not an AME state.
-/

section

open scoped BigOperators

namespace OpenQuantumProblem35

/- ## Basic structures -/

/-- A computational-basis configuration of $n$ parties with local dimension $d$. -/
abbrev Config (n d : ℕ) := Fin n → Fin d

/-- A state vector in the computational basis, viewed as a finite-dimensional Hilbert space. -/
abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)

/-- Build a state vector from its computational-basis amplitudes. -/
abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ

/-- A state vector can be evaluated on a computational-basis configuration to read its amplitude. -/
instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1

/-- Permute the parties of a configuration. -/
def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)

/-- Permute the parties of a state vector. -/
def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)

/--
Merge a configuration on the first $m$ parties and a configuration on the remaining $n-m$
parties into a configuration on all $n$ parties.
-/
def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

/-- The embedding of the first $m$ indices into $\mathrm{Fin}\, n$. -/
def leftIndex {m n : ℕ} (hm : m ≤ n) (i : Fin m) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 hm⟩

/-- The embedding of the last $n-m$ indices into $\mathrm{Fin}\, n$. -/
def rightIndex {m n : ℕ} (hm : m ≤ n) (i : Fin (n - m)) : Fin n :=
  ⟨m + i.1, by omega⟩

/- ## Reduced density matrices and AME -/

/--
The reduced density matrix obtained by tracing out the last $n-m$ parties.

The subsystem is always the first $m$ parties; different subsystems are handled by first
permuting the parties.
-/
noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))

/-- The maximally mixed state on $m$ parties. -/
noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)

/-- A state has maximally mixed reduction on the first $m$ parties. -/
def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d

/--
A state $\psi$ is absolutely maximally entangled.

Standard AME definitions quantify over all subsets $A \subseteq \mathrm{Fin}\, n$ with
$|A| \le \lfloor n/2 \rfloor$ and require that the reduction on $A$ be maximally mixed.
For pure states it is enough to check subsets of size exactly $\lfloor n/2 \rfloor$; see the
references of Helwig--Cui--Riera--Latorre--Lo (2012) and
Goyeneche--Alsina--Latorre--Riera--Życzkowski (2015). In this file, a subsystem of that size is
encoded by first permuting the chosen parties to the front and then tracing out the remaining
parties.

We also require $\psi$ to be normalized explicitly.
-/
def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)

/-- Existence of an $\mathrm{AME}(n,d)$ state. -/
def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : 1 < n), ¬ ExistsAME n 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 1), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ¬ ExistsAME n 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ¬ ExistsAME n 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ¬ ExistsAME n 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ¬ ExistsAME n 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ¬ ExistsAME n 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ¬ ExistsAME n 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ¬ ExistsAME n 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ¬ ExistsAME n 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n < 1)), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ¬ ExistsAME n 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ¬ ExistsAME n 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ¬ ExistsAME n 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ¬ ExistsAME n 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : 0 < n), ¬ ExistsAME n 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : 0 < n), ¬ ExistsAME n 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : 0 < n), ¬ ExistsAME n 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) ↔
    (∀ {n : ℕ} (hn : 0 < n), ¬ ExistsAME n 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ¬ ExistsAME n 0) →
    (∀ {n : ℕ} (hn : n > 1), ¬ ExistsAME n 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
