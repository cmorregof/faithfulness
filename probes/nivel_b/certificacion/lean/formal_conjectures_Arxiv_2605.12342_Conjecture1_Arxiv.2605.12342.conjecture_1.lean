import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Fernandes' conjecture on the 2-generation of even direct product permutation groups

*Reference:* [arxiv/2605.12342](https://arxiv.org/abs/2605.12342)
**Groups of permutations that are even on maximal proper subsets, and related monoids**
*Reference:* 
- [arxiv/2605.12342](https://arxiv.org/abs/2605.12342)
**Groups of permutations that are even on maximal proper subsets, and related monoids**
by *Vítor H. Fernandes*
- [K26](https://github.com/KitaKen1/fernandes-conjecture-1-lean)

For positive integers $m, n \ge 2$, let $\mathrm{S}_m \times \mathrm{S}_n$ be the direct product of
symmetric groups on $[m] = \{1, \dots, m\}$ and $[n'] = \{1', \dots, n'\}$. Define
$$
\Gamma_{m \oplus n} = \{(\sigma_1, \sigma_2) \in \mathrm{S}_m \times \mathrm{S}_n :
  \mathrm{sgn}(\sigma_1) = \mathrm{sgn}(\sigma_2)\}
$$
to be the index-$2$ subgroup of pairs of permutations with equal parity, i.e., those whose
product action on $[m] \cup [n']$ is an even permutation.

It is known that $\mathrm{rank}(\Gamma_{2 \oplus 2}) = 1$, $\mathrm{rank}(\Gamma_{3 \oplus 3}) = 3$,
$\mathrm{rank}(\Gamma_{4 \oplus 3}) = 3$, and $\mathrm{rank}(\Gamma_{4 \oplus 4}) = 3$.

**Conjecture 1 (Fernandes, 2026):** For all integers $m \ge n \ge 2$ such that
$(m, n) \notin \{(2,2), (3,3), (4,3), (4,4)\}$, the group $\Gamma_{m \oplus n}$ has
rank $2$ (i.e., is $2$-generated).
-/

section

namespace Arxiv.«2605.12342»

open Equiv.Perm

/--
The group homomorphism $(\sigma_1, \sigma_2) \mapsto \mathrm{sgn}(\sigma_1) \cdot \mathrm{sgn}(\sigma_2)^{-1}$
from $\mathrm{S}_m \times \mathrm{S}_n$ to $\{+1, -1\}$.

Its kernel is exactly $\Gamma_{m \oplus n}$.
-/
noncomputable def signDiffHom (m n : ℕ) : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) →* ℤˣ :=
  (sign.comp (MonoidHom.fst _ _)) * (sign.comp (MonoidHom.snd _ _))⁻¹

/--
The subgroup $\Gamma_{m \oplus n} \le \mathrm{S}_m \times \mathrm{S}_n$ consisting of all pairs
$(\sigma_1, \sigma_2)$ of permutations with equal signature, i.e.
$\mathrm{sgn}(\sigma_1) = \mathrm{sgn}(\sigma_2)$.

This is the kernel of the sign-difference homomorphism
$(\sigma_1, \sigma_2) \mapsto \mathrm{sgn}(\sigma_1) \cdot \mathrm{sgn}(\sigma_2)^{-1}$,
and is an index-$2$ subgroup of $\mathrm{S}_m \times \mathrm{S}_n$.
-/
noncomputable def gammaSubgroup (m n : ℕ) : Subgroup (Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) :=
  (signDiffHom m n).ker

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (True))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (2 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (2 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (2 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (2 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (2 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (2 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (2 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 3 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (3 ≤ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (3 ≤ m))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (3 ≤ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : m ≥ 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (m ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : m ≥ 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : m ≥ 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : m ≥ 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : m ≥ 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔ (∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁₁, g₂} = ⊤) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hn2 : 2 ≤ n) (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2' : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2' : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2' : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2' : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2' : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : ¬(m < 2)) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (¬(m < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : ¬(m < 2)) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : ¬(m < 2)) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : ¬(m < 2)) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : ¬(m < 2)) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (2 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) ↔
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m > 2) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m > 2))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : m ≥ 3) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (m ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (m ≥ 3))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (m ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 1 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ m) ↔ (1 ≤ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ n) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (1 ≤ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (1 ≤ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (1 ≤ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (1 ≤ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (1 ≤ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((2 ≤ m) ↔ (1 ≤ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 2 < n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 1 < m) (hn2 : 3 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) →
    (∀ {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))), ∃ g₁ g₂ : gammaSubgroup m n, Subgroup.closure {g₁, g₂} = ⊤) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    (2 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (2 ≤ m) ∧ (n ≤ m) ∧ ((m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) ∧ (¬((2 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hmn : n ≤ m) (h_except : (m, n) ∉ ({(2, 2), (3, 3), (4, 3), (4, 4)} : Set (ℕ × ℕ))) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
