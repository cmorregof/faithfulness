import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Elliott–Halberstam conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Elliott%E2%80%93Halberstam_conjecture)
- [EH68] Elliott, Peter D. T. A. and Halberstam, Heini, *A conjecture in prime number
  theory*, Symposia Mathematica, Vol. IV (INDAM, Rome, 1968/69), 59–72.
- [FG89] Friedlander, John and Granville, Andrew, *Limitations to the equi-distribution of
  primes I*, Ann. of Math. (2) 129 (1989), no. 2, 363–382.
-/

section

namespace ElliottHalberstamConjecture

/--
$\pi(x; q, a)$: the number of primes $p \le x$ with $p \equiv a \pmod q$.
-/
def primesInAPCount (x q : ℕ) (a : ZMod q) : ℕ :=
  ((Finset.range (x + 1)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card

/--
The error term
$$E(x; q) = \max_{\gcd(a,q)=1} \left|\pi(x;q,a) - \frac{\pi(x)}{\varphi(q)}\right|,$$
measuring the deviation of the primes in the arithmetic progressions modulo $q$ from
uniform distribution among the $\varphi(q)$ coprime residue classes.
-/
noncomputable def E (x q : ℕ) : ℝ :=
  ⨆ a : (ZMod q)ˣ, |(primesInAPCount x q a : ℝ) - (x.primeCounting : ℝ) / (q.totient : ℝ)|

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ ≤ 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ ≤ 1 / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2))) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ ≤ 1 / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 3) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (θ < 1 / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (θ < 1 / 3))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (θ < 1 / 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : 1 / 2 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (1 / 2 > θ) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : 1 / 2 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : 1 / 2 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : 1 / 2 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : 1 / 2 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔ (∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C₁ > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C₁ * x / Real.log x ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ₀ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ₀ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ₀ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ₀ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ₀ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : ¬(1 / 2 ≤ θ)) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) :
    (θ < 1 / 2) ↔ (¬(1 / 2 ≤ θ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : ¬(1 / 2 ≤ θ)) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : ¬(1 / 2 ≤ θ)) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : ¬(1 / 2 ≤ θ)) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) ↔
    (∀ (θ : ℝ) (hθ : ¬(1 / 2 ≤ θ)) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 2 ≥ θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  simp_all

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 2 ≥ θ) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ))) :=
  ⟨(3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 2 ≥ θ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (θ : ℝ) (hθ : θ < 1 / 2) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) →
    (∀ (θ : ℝ) (hθ : 1 / 3 > θ) (A : ℝ) (hA : 0 < A), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
      ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  simp_all

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hA : 0 < A) :
    (θ < 1 / 2) ↔ (1 / 3 > θ) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(4 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(4 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ) (A : ℝ), (0 < A) ∧ (¬((θ < 1 / 2) ↔ (1 / 3 > θ))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (θ : ℝ), ¬((θ < 1 / 2) ↔ (1 / 3 > θ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hθ : θ < 1 / 2) (hA : 0 < A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hθ : θ < 1 / 2) (hA : 0 < A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hθ : θ < 1 / 2) (hA : 0 < A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hθ : θ < 1 / 2) (hA : 0 < A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (θ : ℝ) (A : ℝ) (hθ : θ < 1 / 2) (hA : 0 < A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
