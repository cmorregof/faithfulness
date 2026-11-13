import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Signed digit sums in bases $b \ge 5$

The sequence is defined by
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.

Generalizing the digit pattern observed in $a(n)$, it was conjectured on the OEIS entry that
for any base $b \ge 5$ and any choice of signs $\pm 1$, the absolute value of $\sum_{k=1}^n \pm b^k$
only contains digits in $\{0, 1, b-2, b-1\}$.

*References:*
- [A243106](https://oeis.org/A243106)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA243106

open Finset

/--
The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b > 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b > 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 6), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 6))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : 5 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (5 ≤ b) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : 5 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : 5 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : 5 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : 5 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k₁ ∈ Icc 1 n, σ k₁ = 1 ∨ σ k₁ = -1),
      let x : Int := (Icc 1 n).sum fun k₁ ↦ σ k₁ * (b : Int) ^ k₁;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k, 1 ≤ k ∧ k ≤ n → σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb₀ : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb₀ : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb₀ : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb₀ : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb₀ : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : ¬(b < 5)), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (¬(b < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : ¬(b < 5)), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : ¬(b < 5)), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : ¬(b < 5)), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : ¬(b < 5)), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) :
    (b ≥ 5) ↔ (b > 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 5 < b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (5 < b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (5 < b))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (5 < b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : 6 ≤ b), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (6 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (6 ≤ b))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (6 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b n : ℕ)  :
    (b ≥ 5) ↔ (b ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((b ≥ 5) ↔ (b ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 5) ↔ (b ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b n : ℕ) (hb : b ≥ 5), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) →
    (∀ (b n : ℕ) (hb : b > 4), ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(6 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(6 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), (b ≥ 5) ∧ (¬(∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ) (n : ℕ), ¬((∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1) ↔ (∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 3 ∨ d = b - 1)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (b n : ℕ) (hb : b ≥ 5) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (b n : ℕ) (hb : b ≥ 5) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (b n : ℕ) (hb : b ≥ 5) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (b n : ℕ) (hb : b ≥ 5) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (b n : ℕ) (hb : b ≥ 5) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
