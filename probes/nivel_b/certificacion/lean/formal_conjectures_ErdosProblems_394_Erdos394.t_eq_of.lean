import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 394

*References:*
- [erdosproblems.com/394](https://www.erdosproblems.com/394)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [ErHa78] Erdős, P. and Hall, R. R., On some unconventional problems on the divisors of integers.
  J. Austral. Math. Soc. Ser. A (1978), 479--485.
-/

section

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Erdos394

/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : v > 0) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (v > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : v > 0) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : v > 0) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : v > 0) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : v > 0) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hv : 0 < v) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hv : 0 < v) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hv : 0 < v) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hv : 0 < v) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hv : 0 < v) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv₀ : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv₀ : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv₀ : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv₀ : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv₀ : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : ¬(v ≤ 0)) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (¬(v ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : ¬(v ≤ 0)) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : ¬(v ≤ 0)) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : ¬(v ≤ 0)) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : ¬(v ≤ 0)) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 1 ≤ v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} :
    (0 < v) ↔ (1 ≤ v) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : 1 ≤ v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : 1 ≤ v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : 1 ≤ v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) ↔
    (∀ {n k v : ℕ} (hv : 1 ≤ v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 1 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (1 < v) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (1 < v))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (1 < v)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (1 < v)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (1 < v)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (1 < v)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (1 < v)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (1 < v)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) →
    (∀ {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))), t k n = v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    (0 < v) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (v : ℕ), (n ∣ ∏ i ∈ range k, (v + i)) ∧ (∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) ∧ (¬((0 < v) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (v : ℕ), ¬((0 < v) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k v : ℕ} (hv : 0 < v) (hdvd : n ∣ ∏ i ∈ range k, (v + i)) (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
