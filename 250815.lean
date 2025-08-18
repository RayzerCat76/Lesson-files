 import Mathlib.Tactic
 import Mathlib.Data.Real.Irrational

 example : (p ∧ q) → (∀ a : Nat, p) ∨ (∃ a : Nat, q) := by
  intro h
  left
  intro a
  exact h.1

section

example : ∃ n : ℕ, n + 2 > 5 := by
  use 4
  simp

example (p q r s : Prop) (h₁ : p ∧ q ∧ r) (h₂ : r → s) : s := by
  rcases h₁ with ⟨a, b, c⟩
  apply h₂ c

example (p q r s t : Prop) (h : ((p ∧ t) ∨ q ∧ ¬r) ∧ (r ∨ (s∧ t))) : t := by
  rcases h with ⟨a, b⟩ 
  · cases' a with a₁ a₂  
    apply And.right
    assumption
    cases' b
    cases a₂
    contradiction
    apply And.right
    assumption


example (p q r : Prop) (h : q → r) : p ∨ q → p ∨ r := by
  intro a
  cases a
  left
  assumption
  right
  apply h
  assumption

  
end

section exercise

example (hnp : ¬p) (hq : q) (hqp : q → p) : r := by
  by_contra
  apply hnp
  apply hqp
  exact hq
  

/-- Don't forget `push_neg`!! -/
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro a
  push_neg at a
  by_cases hp: p
  · right
    exact a hp
  · left
    exact hp

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  · intro h₁ h₂
    exact h₁ h₂.1 h₂.2
  · intro h₁ h₂ h₃
    have : p ∧ q := by exact ⟨h₂, h₃⟩
    exact h₁ this

/-- **Boss level** -/
example (p : Prop) {s} : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro h
  by_cases hp : p
  · cases' h hp with hr hs
    · left
      intro _
      exact hr
    · right
      intro _
      exact hs
  exact imp_or'.mp h
end exercise

section exercise

variable (α : Type) (p q : α → Prop) (r : Prop)
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z := by
  use y
/-- A little bit hard. -/
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  intro h
  rcases h with ⟨x, (hp | hq)⟩
  left
  use x
  right
  use x
  intro h
  rcases h with ⟨x, hp⟩ | ⟨x, hq⟩
  use x
  constructor
  exact hp
  use x
  right
  exact hq



/-- Very hard. -/
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  · intro h₁ h₂
    rcases h₁ with ⟨x, h₁₁⟩
    exact h₁₁ (h₂ x)
  · intro h₁
    by_cases h₂ : ∀ x : a, p x
    · use a
      intro h
      exact h₁ h₂
    · push_neg at h₂
      rcases h₂ with ⟨x, hp⟩
      use x
      intro h
      contradiction

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases' h with hp hq
  · left
    exact hp x
  · right
    exact hq x


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)
/--
Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction: -/
example (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False := by
  
  

end exercise
namespace proof

theorem classical_em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := (x = True) ∨ p
  let V (x : Prop) : Prop := (x = False) ∨ p
  have exU : ∃ x, U x := by
    use True
    unfold U
    left
    rfl
  have exV : ∃ x, V x := by
    use False
    unfold V
    left
    rfl
  let u : Prop := Classical.choose exU
  let v : Prop := Classical.choose exV
  have u_def : U u := Classical.choose_spec exU
  have v_def : V v := Classical.choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p := by
    unfold U at u_def
    unfold V at v_def
    cases' u_def with hu hp
    · cases' v_def with hv hp'
      · left
        rw [hu]
        rw [hv]
        exact true_ne_false
      · right
        exact hp'
    · right
      exact hp
  have p_implies_uv : p → u = v := by
    intro hp
    have U_eq_V : U = V := by
      unfold U V
      ext x
      constructor
      · intro h
        right
        exact hp
      · intro h
        right
        exact hp
    have : ∀ exU exV, @Classical.choose _ U exU = @Classical.choose _ V exV := by
      rw [U_eq_V]
      intro exu exv
      rfl
    unfold u v
    exact this exU exV
  cases' not_uv_or_p with hne hp
  · right
    by_contra hp
    have he : u = v := by exact p_implies_uv hp
    contradiction
  · left
    exact hp

end proof 
