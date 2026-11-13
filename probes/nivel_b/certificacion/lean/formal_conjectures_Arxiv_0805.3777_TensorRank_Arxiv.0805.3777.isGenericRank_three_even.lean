import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Generic and maximal rank of 3-tensors

The rank of a tensor $T \in \mathbb{C}^{m_1} \otimes \mathbb{C}^{m_2} \otimes \mathbb{C}^{m_3}$ is
the least $r$ such that $T$ is a sum of $r$ decomposable tensors $a \otimes b \otimes c$. Mathlib
records such a tensor as a `Holor ℂ [m₁, m₂, m₃]` and its rank as `Holor.cprank`.

Two basic invariants of the format $(m_1, m_2, m_3)$ are the *generic rank*
$\operatorname{grank}(m_1, m_2, m_3)$, the rank of a generic tensor, and the *maximal rank*
$\operatorname{mrank}(m_1, m_2, m_3)$, the largest rank attained by a tensor of that format.

Counting parameters gives the lower bound
$\operatorname{grank}(m_1, m_2, m_3) \geq r_0(m_1, m_2, m_3) :=
\lceil m_1m_2m_3 / (m_1 + m_2 + m_3 - 2) \rceil$. Once $m_3$ exceeds $(m_1-1)(m_2-1)$ the generic
rank is known to be $\min(m_3, m_1m_2)$, so the interesting case is the *critical range*
$3 \leq m_1 \leq m_2 \leq m_3 \leq (m_1-1)(m_2-1)$ [Fri12, Conjecture 5.1; BFZ24, (4.14)]. There
the bound $r_0$ is attained in every case that has been settled, except for the formats
$(3, 2p+1, 2p+1)$, where the generic rank is $r_0 + 1$. Friedland's conjecture, stated here as
`isGenericRank_of_le_critical`, is that these are the only exceptions.

The maximal rank is much less well understood. It is known for the formats
$2 \times m \times n$ and for a range of small formats, but no formula is known even for
$(n, n, n)$, and $\operatorname{mrank}(3, 3, 5)$ is undetermined.

Tensor rank is invariant under permuting the three factors, but `Holor ℂ [m₁, m₂, m₃]` and its
permutations are different types and Mathlib has no transport lemma between them. Each statement
below therefore writes the format in the order its own source uses.

*References:*
* [Fri12] S. Friedland, *On the generic and typical ranks of 3-tensors*, Linear Algebra Appl. 436
  (2012), 478-497, https://doi.org/10.1016/j.laa.2011.05.008
  ([arxiv/0805.3777](https://arxiv.org/abs/0805.3777)). Conjecture 5.1, and the survey of known
  values in Section 5.
* [BFZ24] W. Bruzda, S. Friedland, K. Życzkowski, *Rank of a tensor and quantum entanglement*,
  Linear Multilinear Algebra 72 (2024), 1796-1859,
  https://doi.org/10.1080/03081087.2023.2211717
  ([arxiv/1912.06854v4](https://arxiv.org/pdf/1912.06854v4)). A survey; the numbering used below is
  that of the arXiv v4 PDF. Conjecture 4.12 restates [Fri12, Conjecture 5.1], and Sections 4.5
  and 4.6 collect the current status.
* [CGG02] M. V. Catalisano, A. V. Geramita, A. Gimigliano, *Ranks of tensors, secant varieties of
  Segre varieties and fat points*, Linear Algebra Appl. 355 (2002), 263-285,
  https://doi.org/10.1016/S0024-3795(02)00352-X. Used for `isGenericRank_of_gt_critical`.
* [Str83] V. Strassen, *Rank and optimal computation of generic tensors*, Linear Algebra Appl.
  52/53 (1983), 645-685, https://doi.org/10.1016/0024-3795(83)80041-X. Used for
  `isGenericRank_three_even` and `isGenericRank_three_odd`.
* [AOP09] H. Abo, G. Ottaviani, C. Peterson, *Induction for secant varieties of Segre varieties*,
  Trans. Amer. Math. Soc. 361 (2009), 767-792, https://doi.org/10.1090/S0002-9947-08-04725-9.
  Used for `isGenericRank_four`.
* [Lic85] T. Lickteig, *Typical tensorial rank*, Linear Algebra Appl. 69 (1985), 95-120,
  https://doi.org/10.1016/0024-3795(85)90070-9. Used for `isGenericRank_cube`.
* [AS79] M. D. Atkinson, N. M. Stephens, *On the maximal multiplicative complexity of a family of
  bilinear forms*, Linear Algebra Appl. 27 (1979), 1-8,
  https://doi.org/10.1016/0024-3795(79)90026-0. Used for `isMaxRank_two`,
  `cprank_le_of_three_slices`, `cprank_le_of_square_slices`, `isMaxRank_of_le_min` and
  `isMaxRank_three_three_five_bounds`.
* [JaJa79] J. JáJá, *Optimal evaluation of pairs of bilinear forms*, SIAM J. Comput. 8 (1979),
  443-462, https://doi.org/10.1137/0208037, and J. B. Kruskal, *Rank, decomposition, and
  uniqueness for 3-way and N-way arrays*, in Multiway Data Analysis, North-Holland (1989), 7-18.
  Cited by [Fri12] for `isMaxRank_two`.
* [SMS10] T. Sumi, M. Miyazaki, T. Sakata, *About the maximal rank of 3-tensors over the real and
  the complex number field*, Ann. Inst. Statist. Math. 62 (2010), 807-822,
  https://doi.org/10.1007/s10463-010-0294-5 ([arxiv/0806.4048](https://arxiv.org/abs/0806.4048)).
  Theorem 4.5 proves the first of the two bounds that [AS79] states without proof; Proposition
  4.9(1) is the special case used for `isMaxRank_three`.
* [Ki26] K. Kitamura, *A Lean proof that the maximal rank of complex $3 \times 3 \times 5$
  tensors is 6*, GitHub repository (2026), https://github.com/KitaKen1/mrank-3-3-5-lean. Used
  for `isMaxRank_three_three_five`.
* [BT15] G. Blekherman, Z. Teitler, *On maximum, typical and generic ranks*, Math. Ann. 362
  (2015), 1021-1031, https://doi.org/10.1007/s00208-014-1150-3
  ([arxiv/1402.2371](https://arxiv.org/abs/1402.2371)), Theorem 1. Used for
  `isMaxRank_le_two_mul_isGenericRank`.
-/

section

namespace Arxiv.«0805.3777»

/-- The space of complex tensors of a fixed format, topologised as the finite-dimensional complex
vector space that it is. -/
noncomputable scoped instance instTopologicalSpaceHolor {ds : List ℕ} :
    TopologicalSpace (Holor ℂ ds) :=
  inferInstanceAs <| TopologicalSpace (HolorIndex ds → ℂ)

/--
`IsGenericRank ds r` says that `r` is the generic rank of complex tensors of format `ds`: the
tensors of rank `r` contain a dense open set.

This is the form the sources establish: the tensors of rank other than the generic rank lie in a
proper algebraic subset [Fri12, Theorem 3.4]. It determines `r` uniquely, by
`IsGenericRank.unique`.
-/
def IsGenericRank (ds : List ℕ) (r : ℕ) : Prop :=
  ∃ U : Set (Holor ℂ ds), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank = r

/--
`IsMaxRank ds r` says that `r` is the maximal rank of a complex tensor of format `ds`: every such
tensor has rank at most `r`, and some tensor has rank `r`.
-/
def IsMaxRank (ds : List ℕ) (r : ℕ) : Prop :=
  IsGreatest (Set.range fun T : Holor ℂ ds => T.cprank) r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (2 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (2 < p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (2 < p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (2 < p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (2 < p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (2 < p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (2 < p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (2 < p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (2 < p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (2 < p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (2 < p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (2 < p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (2 < p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 3 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : p ≥ 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : p ≥ 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : p ≥ 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : p ≥ 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : p ≥ 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp₀ : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp₀ : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp₀ : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp₀ : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp₀ : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : ¬(p < 2)), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : ¬(p < 2)), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : ¬(p < 2)), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : ¬(p < 2)), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : ¬(p < 2)), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 1 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {p : ℕ} :
    (2 ≤ p) ↔ (1 < p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p > 2), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : p ≥ 3), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p : ℕ}  :
    (2 ≤ p) ↔ (1 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (1 ≤ p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (1 ≤ p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (1 ≤ p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (1 ≤ p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (1 ≤ p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (1 ≤ p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (1 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (1 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (1 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (1 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (1 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (1 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p : ℕ} (hp : 2 ≤ p), IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) →
    (∀ {p : ℕ} (hp : 1 < p), IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(13 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((IsGenericRank [3, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1))) ↔ (IsGenericRank [4, 2 * p, 2 * p] (12 * p ^ 2 ⌈/⌉ (4 * p + 1)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {p : ℕ} (hp : 2 ≤ p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {p : ℕ} (hp : 2 ≤ p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {p : ℕ} (hp : 2 ≤ p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {p : ℕ} (hp : 2 ≤ p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {p : ℕ} (hp : 2 ≤ p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
