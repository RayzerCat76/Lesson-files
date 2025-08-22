import Mathlib

namespace Exam

def dvd : ℕ → ℕ → Prop :=
  fun d n => ∃ m : ℕ, n = d * m

/- **`Problem 1`** -/
instance dvd_partial_order : PartialOrder ℕ where
  le :=
    fun a b => dvd a b
  lt :=
    fun a b => (dvd a b) ∧ ¬(dvd b a)
  le_refl := by 
    intro a
    use 1
    exact Eq.symm (Nat.mul_one a)
  le_trans := by
    intro d n n₁ dn nn₁
    simp[dvd]
    rcases dn with ⟨dnf, dns⟩
    rcases nn₁ with ⟨nn₁f, nn₁s⟩
    rw[nn₁s, dns]
    use dnf * nn₁f
    rw[Nat.mul_assoc]

  le_antisymm := by
    intro d n m m₁
    rcases m with ⟨mf, ms⟩
    rcases m₁ with ⟨m₁f, m₁s⟩
    nth_rw 1 [ms]
    have pre : mf * m₁f = 1 := by
      sorry
    have : mf = 1 := by
      sorry
    rw[this]
    simp
-- `≼` is the partial order we defined above, i.e. `a ≼ b ↔ a is divided by b`. Please distinguish `≼` from `≤`, which is the standard order on `ℕ`. You can use `\preceq` to get `≼`.
infixl:100 " ≼ " => @LE.le _ dvd_partial_order.toLE
lemma dvd_equiv {a b : ℕ} : a ≼ b ↔ a ∣ b := Eq.to_iff rfl

/- **`Problem 2`** -/
theorem le_of_ne_zero_of_dvd (d n : ℕ) (hn : n ≠ 0) (h : d ≼ n) : d ≤ n := by
  rcases h with ⟨m, h⟩
  have hm : m ≠ 0 := by
    apply Nat.ne_zero_of_mul_ne_zero_left
    rw[mul_comm, ← h]
    exact hn
  rw[h]
  

/- **`Problem 3`** -/
theorem exists_least_element : ∃ n : ℕ, ∀ m : ℕ, n ≼ m := by
  use 1
  intro a
  

/- **`Problem 4`** -/
theorem exists_greatest_element : ∃ n : ℕ, ∀ m : ℕ, m ≼ n := by
  sorry

open Fin NatCast
/- **`Problem 5`** -/
theorem exists_supremum_ofInfinite (A : Set ℕ) (hA : A.Infinite) :
  ∃ n : ℕ, (∀ x ∈ A, x ≼ n) ∧
    ∀ m : ℕ, (∀ x ∈ A, x ≼ m) →
      n ≼ m := by
  use 0
  constructor
  · intro a b

  · intro m hm
    by_cases h₁ : m = 0
    · use 0
    · have h₂ : ∃ x ∈ A, m < x := by
        by_contra! h
        let f : ℕ → Fin (m + 1) :=
          fun n => (n : Fin (m + 1))
        have hf₁ : A.MapsTo f Set.univ := sorry
        have hf₂ : A.InjOn f := by
          intro x mem_x y mem_y hf
          rw [← Fin.val_inj] at hf
          simp only [f, Fin.val_natCast] at hf
          rw [Nat.mod_eq_of_lt (Nat.lt_succ.mpr (h x mem_x))] at hf
          rw [Nat.mod_eq_of_lt (Nat.lt_succ.mpr (h y mem_y))] at hf
          exact hf
        sorry
      rcases h₂ with ⟨x, mem, hx⟩
      exfalso
      sorry

/- **`Problem 6`** -/
def M (A : Set {x : ℕ // x ≠ 0}) : Set {x : ℕ // x ≠ 0} :=
  {n : {x : ℕ // x ≠ 0} | ∀ d ∈ A, d ≼ n}

/- **`Problem 6.1`** -/
open Nat in
theorem M_nonempty (A : Set {x : ℕ // x ≠ 0}) (hA₁ : A.Nonempty) (hA₂ : A.Finite) : (M A).Nonempty := by
  obtain ⟨a, mem, h⟩ := Set.exists_max_image A id hA₂ hA₁
  let n := (a.val)!
  have hn : n ≠ 0 := by
    simp
    exact factorial_ne_zero ↑a
  use ⟨n, hn⟩
  simp only [M, Set.mem_setOf]
  intro a b
  constructor
  sorry

/- **`Problem 6.2`** -/
theorem least_element_property (A : Set {x : ℕ // x ≠ 0}) (_ : A.Nonempty) (_ : A.Finite) (n₀ : {x : ℕ // x ≠ 0}) (hn₁ : n₀ ∈ M A) (hn₂ : ∀ n ∈ M A, n₀.val ≤ n.val) : ∀ n ∈ M A, n₀ ≼ n := by
  by_contra! h
  rcases h with ⟨m,hm⟩
  let n' := m.val % n₀.val
  have n'_neq_zero : n' ≠ 0 := sorry
  have hn' : ⟨n',n'_neq_zero⟩ ∈ M A := by
    intro d hd
    simp [n']
    rcases hm.1 d hd with ⟨t₁,ht₁⟩
    rcases hn₁ d hd with ⟨t₂,ht₂⟩
    have hnew : d.val * (m.val / n₀.val * t₂) + m.val % n₀.val = d.val * t₁ := by
      sorry
    sorry
  have hfinal : n' < n₀.val := sorry
  sorry

/- **`Problem 6.3`** -/
theorem exists_suprenum_ofFinite (A : Set {x : ℕ // x ≠ 0}) (hA₁ : A.Nonempty) (hA₂ : A.Finite) (n₀ : {x : ℕ // x ≠ 0}) (hn₁ : n₀ ∈ M A) (hn₂ : ∀ n ∈ M A, n₀.val ≤ n.val) :
  ∃ nₘ : {x : ℕ // x ≠ 0},
    (∀ a ∈ A, a.val ≼ nₘ.val) ∧
      ∀ n : {x : ℕ // x ≠ 0}, (∀ a ∈ A, a.val ≼ n.val) → nₘ ≼ n := by
  sorry

end Exam
