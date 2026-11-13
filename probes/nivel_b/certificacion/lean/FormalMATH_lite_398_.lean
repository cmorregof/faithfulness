import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Finset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔ ({t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, b * t = k₁ ∧ c * t = k₁}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, c * t = k₁ ∧ a * t = k₁}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k₁ : ℤ, a * t = k₁ ∧ b * t = k₁ ∧ c * t = k₁}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (hb : 0 < b) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha₀ : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : ¬(a ≤ 0)) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) ↔
    (∀ (a b c : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < a) ↔ (1 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < b) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℕ) (ha : 0 < a) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) →
    (∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (d1 d2 d3 d : ℕ) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c), {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, b * t = k ∧ c * t = k}.ncard -
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, c * t = k ∧ a * t = k}.ncard +
    {t : ℝ | t ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a * t = k ∧ b * t = k ∧ c * t = k}.ncard =
    a + b + c - d1 - d2 - d3 + d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    (0 < b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ) (d1 : ℕ) (d2 : ℕ) (d3 : ℕ) (d : ℕ), (0 < a) ∧ (0 < c) ∧ (d1 = Nat.gcd a b) ∧ (d2 = Nat.gcd b c) ∧ (d3 = Nat.gcd c a) ∧ (d = Nat.gcd (Nat.gcd a b) c) ∧ (¬((0 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((0 < b) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((0 < b) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((0 < b) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((0 < b) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((0 < b) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((0 < b) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℕ) (d1 d2 d3 d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd1 : d1 = Nat.gcd a b) (hd2 : d2 = Nat.gcd b c) (hd3 : d3 = Nat.gcd c a) (hd : d = Nat.gcd (Nat.gcd a b) c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
