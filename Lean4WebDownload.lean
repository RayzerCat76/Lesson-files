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
  