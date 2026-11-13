import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Schur's theorem on Galois groups of truncated exponential polynomials

*Reference:* (https://math.stackexchange.com/questions/2814220)

*Reference* (https://mathoverflow.net/questions/477077)
-/

section

/-
Note: This was asked by Nick Katz. Quasi-autoformalized using Claude 4.0 Sonnet.
-/

namespace SchurTruncatedExponential

open Polynomial

open scoped Nat

/--
The truncated exponential polynomial `truncatedExp n` is
given by `∑_{j=0}^{n} x^j / j!` over `ℚ`, which is the
`n`-th partial sum of the Taylor series for the exponential function `e^x`.
-/
noncomputable def truncatedExp (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), (1 / j ! : ℚ) • X ^ j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 3), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn₀ : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn₀ : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn₀ : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn₀ : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n ≥ 2) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 2 < n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n ≥ 2) ↔ (n ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n ≥ 2) ↔ (n ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≥ 2) ↔ (n ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) →
    (∀ (n : ℕ) (hn : n > 1), letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≥ 2) ∧ (¬(letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n))) ↔ (letI f := truncatedExp n
  if n % 5 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n ≥ 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n ≥ 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n ≥ 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n ≥ 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n ≥ 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
