import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

-- # §1: Sets

open scoped Set
section Definitions


-- **An error**
example (S : Set) := sorry
example {α : Type} (S : Set α) : S = S := rfl


-- `⌘`


-- **A tautology**

-- **ToDo**
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  sorry


-- **The positive integers**
-- **ToDo**
def PositiveIntegers : Set ℤ := by
  sorry

-- `⌘`

-- **ToDo**
lemma one_posint : 1 ∈ PositiveIntegers := by
  sorry

-- **ToDo**
def PositiveNaturals : Set ℕ := by
  exact (0 < ·)

-- **ToDo**
example : 1 ∈ PositiveNaturals := by
  sorry

-- **ToDo**
-- Why does this *fail*? How to fix it?
example : (-1) ∉ PositiveNaturals := sorry


-- **ToDo**
def EvenNaturals : Set ℕ := by
  sorry

-- **ToDo**
example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  sorry


-- **ToDo**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

-- **ToDo**
-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  sorry


-- `⌘`


-- **ToDo**
-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by
  sorry

-- **ToDo**
example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  sorry


-- **Another take on subsets and sets as types**

-- **ToDo**
def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := P

-- **ToDo**
def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  sorry

-- Are they *equal*? This is an exercise below.

-- **ToDo**
-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (hx : x ∈ subsub P) : x ∈ S := sorry


-- **What is really this "injection"  `Set α ↪ Type`?**

-- **ToDo?**
-- Why does this *fail*? How to fix it?
example : ∀ n : PositiveIntegers, 0 ≤ n := sorry


/- **§ Some exercises** -/

-- **Exercise**
example : 1 ∉ EvenNaturals := by
  sorry

-- **Exercise**
example : -1 ∉ PositiveIntegers := by
  sorry

-- **Exercise**
-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := by
  sorry

-- **Exercise**
-- Why does this *fail*? How to fix it?
example : 1 ∉ EvenPositiveNaturals := sorry


-- **Exercise**
-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := sorry

-- **Exercise**
example : 3 ∈ OddNaturals := by
  sorry

-- **Exercise**
example (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  sorry


-- **Exercise**
-- Why does this *fail*?
example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions


-- `⌘`


-- ## Operations on sets

section Operations

-- **Self-intersection is the identity, proven with extensionality**
-- **ToDo**
example (α : Type) (S : Set α) : S ∩ S = S := by
  sorry


-- `⌘`


-- **The union**
-- **ToDo**
example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  sorry


-- **An _unfixable_ problem**
-- **ToDo**
example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry
/- *Sol.:*  Well, it was unfixable, so there is no solution...-/


-- `⌘`


-- **Empty set**

-- **ToDo**
example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  sorry


-- `⌘`


-- **§ Indexed unions**

-- **ToDo**
example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  sorry


/- **§ Some exercises** -/

-- **Exercise**
-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  sorry

-- **Exercise**
example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  sorry

-- **Exercise**
example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  sorry

-- **Exercise**
-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  sorry

-- **Exercise**
-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  sorry

-- **Exercise**
-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  sorry


-- **Exercise**
example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  sorry


-- **Exercise**
-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry


-- **Exercise**
example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  sorry

end Operations


-- `⌘`


-- # §2: Functions

-- **ToDo**
-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
  f = g ↔ ∀ a : α, a ∈ S → f a  = g a := by sorry


-- `⌘`


section Operations

open Function

variable (α β : Type) (f : α → β)

-- The **image**

-- **ToDo**
example : 1 ∈ Nat.succ '' univ := by
  sorry

-- **ToDo**
-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  sorry


-- **ToDo**
example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  sorry


-- `⌘`


-- The **preimage**

-- **ToDo**
example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  sorry

-- `⌘`

-- **ToDo**
example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  sorry


-- Observe that `obtain` does not work here
-- **ToDo**
example (b : β) (hf : Surjective f) : α := by sorry




/- **§ Some exercises** -/

open Function

-- **Exercise**
/- The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  sorry

-- **Exercise**
-- Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) := sorry

-- **Exercise**
-- Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by sorry

-- **Exercise**
-- Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  sorry


-- **Exercise**
/- The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
  sorry


-- **Exercise**
/- The complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  sorry

end Operations
