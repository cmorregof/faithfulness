import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Mahler's 3/2 Problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Mahler%27s_3/2_problem)
-/

section

namespace Mahler32

/-- For a real number `α`, define `Ω(α)` as
$$
\Omega (\alpha )=\inf _{\theta > 0}\left({\limsup _{n\rightarrow \infty }\left\lbrace
{\theta \alpha ^{n}}\right\rbrace -\liminf _{n\rightarrow \infty }\left\lbrace {\theta \alpha ^{n}}\right\rbrace }\right).
$$
-/
noncomputable def Ω (α : ℝ) : ℝ :=
  sInf {Filter.atTop.limsup (fun n ↦ Int.fract (θ * α ^ n))
    - Filter.atTop.liminf (fun n ↦ Int.fract (θ * α ^ n)) | (θ : ℝ) (_ : 0 < θ)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (q > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≥ 1 / p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hpq : p.Coprime q) (hq : 1 < q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hq : 1 < q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hq : 1 < q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hq : 1 < q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hq : 1 < q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq₀ : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq₀ : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq₀ : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq₀ : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq₀ : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : ¬(q ≤ 1)) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (¬(q ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : ¬(q ≤ 1)) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : ¬(q ≤ 1)) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : ¬(q ≤ 1)) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : ¬(q ≤ 1)) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) :
    (1 < q) ↔ (2 ≤ q) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) ↔
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q ≥ 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (q ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (q ≥ 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (q ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (q ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (q ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (q ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (q ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (q ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : q > 1) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) > 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) > 1 / p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≥ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (1 ≤ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (1 ≤ q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (1 ≤ q)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), Ω (p / q) ≤ 1 / p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (Ω (p / q) ≤ 1 / p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p < Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p < Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q ≤ p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) :
    (q < p) ↔ (q ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (¬((q < p) ↔ (q ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((q < p) ↔ (q ≤ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (2 < q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (2 < q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (2 < q)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (2 < q)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (2 < q)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (2 < q)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (2 < q)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (2 < q)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 3 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (3 ≤ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (3 ≤ q))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (3 ≤ q)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 2 ≤ q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≥ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (1 < q) ∧ (p.Coprime q) ∧ (q < p) ∧ (¬(1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), ¬((1 / p ≤ Ω (p / q)) ↔ (1 / p ≥ Ω (p / q))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) →
    (∀ (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p), 1 / p ≤ Ω (p / q)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hpq : p.Coprime q) (hpq' : q < p) :
    (1 < q) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Coprime q) ∧ (q < p) ∧ (¬((1 < q) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((1 < q) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p q : ℕ) (hq : 1 < q) (hpq : p.Coprime q) (hpq' : q < p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
