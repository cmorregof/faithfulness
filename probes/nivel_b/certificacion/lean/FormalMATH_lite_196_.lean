import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q ≤ 2005) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q ≤ 2005))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q ≤ 2005)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2006) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2006) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2006))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(2007 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2006)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (2005 > q) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp₀ : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp₀ : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp₀ : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp₀ : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp₀ : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : ¬(2005 ≤ q)) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (¬(2005 ≤ q)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : ¬(2005 ≤ q)) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : ¬(2005 ≤ q)) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : ¬(2005 ≤ q)) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : ¬(2005 ≤ q)) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} :
    (q < 2005) ↔ (q ≤ 2004) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) ↔
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2005 ≥ q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2005 ≥ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2005 ≥ q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2005 ≥ q)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : 2006 > q) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (2006 > q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (2006 > q))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(2007 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (2006 > q)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p ≤ 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p ≤ 2005) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p ≤ 2005))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p ≤ 2005)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2004) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (q < 2004) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (q < 2004))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (q < 2004)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q ≤ 2004) (h2 : p < 2006) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (p < 2005) ↔ (p < 2006) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (q < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((p < 2005) ↔ (p < 2006))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(2007 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p < 2005) ↔ (p < 2006)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) →
    (∀ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4), (p = 2 ∧ q = 2) ∨ (p = 5 ∧ q = 29) ∨ (p = 29 ∧ q = 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    (q < 2005) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(1 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(1 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(3 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(1 : ℕ), (2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(3 : ℕ), (2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(4 : ℕ), (2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2005 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2004 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2006 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (q : ℕ), (p.Prime) ∧ (q.Prime) ∧ (p < 2005) ∧ (q ∣ p ^ 2 + 4) ∧ (p ∣ q ^ 2 + 4) ∧ (¬((q < 2005) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2005 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2004 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2006 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℕ), ¬((q < 2005) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : q < 2005) (h2 : p < 2005) (h3 : q ∣ p ^ 2 + 4) (h4 : p ∣ q ^ 2 + 4) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
