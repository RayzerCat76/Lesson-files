import Mathlib.Tactic

theorem example1 : True := by 
  trivial

theorem example2 (P : Prop) (h : False) : P := by
  trivial

example (q: Q) : P → Q := by
  intro p
  exact q

example (h: 2 < 3) (i : 3 < 5) : 3 < 5 → 2 < 3 := by
  intro
  exact h

example (h: 3 < 5) (i: 3 < 5 → 2 < 3) : 2 < 3 := by
  grind
  
example ( P Q R : Prop) (p : P) (h : Q → R) (j : P → Q) : R:= by
  grind

example (h : P → False) : ¬P := by
  intro x
  apply h
  exact x
  -- grind

example(p : P) (h : ¬P) : False := by
  contradiction
  -- grind

example (p : 2 < 3) (q : 2 ≥ 3) : 5 < 3 := by
  contradiction
  -- grind
example (p : ¬¬P) : P := by
  apply by_contradiction
  exact p
  -- grind

#check by_contradiction --classical logic

section Forall

#check ∀ (n : Nat), n > 100
#check ∀ n : Nat, n > 100
#check ∀ n, n > 100

example : ∀ (n : Nat), n >= 0 := by
  exact Nat.zero_le

example (p : ∀ (n : Nat), n > 100) : 5 > 100 := by 
  apply p

example : ∃ (n: Nat), n > 100 := by
  use 120
  trivial

example (n m : Nat) (p : n > m) : ∃ (x : Nat), x > m := by
  use n

example (P : Prop) (h : ∃ (x : Nat), P) : P := by
  rcases h with ⟨n, p⟩ 
  exact p
example (n m : Nat) (h : m = n) (p : ∃(x : Nat), x > n): ∃(x : Nat), x > m := by
  rcases p with ⟨a, b⟩ 
  rw[h]
  use a

end Forall

section and_or

example (x : Nat) (h : x ≥ 4 ∧ x < 6 ∧ x ≠ 5) : x = 4 := by
  rcases h with ⟨h1, h2, h3⟩ 
  apply Nat.le_antisymm
  show x ≥ 4
  exact h1
  apply Nat.le_of_lt_succ
  simp
  apply Nat.lt_of_le_of_ne
  apply Nat.le_of_lt_succ
  simp
  apply h2
  exact h3
  
-- example (x : Nat) (h : x = 5) : x ≥ 5 ∧ x < 6 := by
--   constructor
--   show x < 6
--   apply Nat.le_of_lt_succ
--   simp
  
--   apply Nat.lt_or_eq_of_le

example : ∀ n : ℕ, n ≥ 0 := by
  exact zero_le

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩ 

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by
  constructor
  apply hpq
  apply hqp

example (n : ℕ) : n ≥ 0 ∨ False := by
  left
  simp

example (n : ℕ) : n < 0 ∨ 1 = 1 := by
  right
  rfl

example (p q r : Prop) (hpq : p ∧ q) (hr : r) : p ∧ r := by
  exact ⟨hpq.left, hr⟩ 

example (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  rcases h with ⟨a, b⟩ 
  apply a hp

example (p q r : Prop) (hpq : p ∨ q) (h : q → r) : p ∨ r := by
  rcases hpq
  left
  assumption
  right
  apply h
  assumption

example {α : Type} (q : Prop) (p : α → Prop) (h₁ : ∃ a, p a) (h₂ : ∀ a, p a → q) : q := by
  rcases h₁ with ⟨x, y⟩
  apply h₂
  assumption

example (p q r s : Prop) (h₁ : p ∧ q ∧ r) (h₂ : r → s) : s := by
  rcases h₁ with ⟨a, b, c⟩
  apply h₂ c
  

example (p q r : Prop) (h : q → r) : p ∨ q → p ∨ r := by
  intro g
  cases g
  left
  assumption
  right
  apply h
  assumption
    
