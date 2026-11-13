import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Berge–Fulkerson conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [Fu71] Fulkerson, D. R. (1971). "Blocking and anti-blocking pairs of polyhedra."
  *Math. Programming* 1, pp. 168--194.
* [Se79] Seymour, P. D. (1979). "On multi-colourings of cubic graphs, and conjectures of
  Fulkerson and Tutte." *Proc. London Math. Soc.* 38, pp. 423--460.
* [Ma11] Mazzuoccolo, G. (2011). "The equivalence of two conjectures of Berge and Fulkerson."
  *J. Graph Theory* 68, pp. 125--128.
* [FR94] Fan, G. and Raspaud, A. (1994). "Fulkerson's conjecture and circuit covers."
  *J. Combin. Theory Ser. B* 61, pp. 133--138.
* [Pe91] Petersen, J. (1891). "Die Theorie der regulären graphs." *Acta Math.* 15,
  pp. 193--220.
-/

section

open SimpleGraph Finset

namespace BergeFulkersonConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is **cubic** if every vertex has degree `3`. -/
def IsCubic (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3

open Classical in
/-- A family of `k` perfect matchings of `G` **covers every edge exactly `m` times** if each
member is a perfect matching and every edge of `G` lies in exactly `m` of them. -/
def IsPerfectMatchingCover (G : SimpleGraph V) (k m : ℕ) (M : Fin k → G.Subgraph) : Prop :=
  (∀ i, (M i).IsPerfectMatching) ∧
    ∀ e ∈ G.edgeSet, (univ.filter fun i => e ∈ (M i).edgeSet).card = m

open Classical in
omit [Fintype V] [DecidableEq V] in

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m < k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m < k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≥ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (m ≥ k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≥ m

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (k ≥ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≥ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≥ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≥ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≥ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM₀ : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM₀ : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM₀ : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM₀ : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM₀ : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), ¬(k < m)

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} :
    (m ≤ k) ↔ (¬(k < m)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), ¬(k < m)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), ¬(k < m)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), ¬(k < m)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) ↔
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), ¬(k < m)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k > m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k > m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), m ≤ k) →
    (∀ {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet), k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((m ≤ k) ↔ (k ≤ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} (hM : IsPerfectMatchingCover G k m M) (he : e ∈ G.edgeSet) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} (hM : IsPerfectMatchingCover G k m M) (he : e ∈ G.edgeSet) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} (hM : IsPerfectMatchingCover G k m M) (he : e ∈ G.edgeSet) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} (hM : IsPerfectMatchingCover G k m M) (he : e ∈ G.edgeSet) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph} {e : Sym2 V} (hM : IsPerfectMatchingCover G k m M) (he : e ∈ G.edgeSet) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
