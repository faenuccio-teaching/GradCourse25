import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

open Set Topology Filter Classical Real

open scoped Filter

#print Filter

variable {α β : Type*}

-- If `a : α`, the set of sets containing `a` is a filter
-- **ToDo**
example (a : α) : Filter α where
  sets := {A | a ∈ A}
  univ_sets := sorry
  sets_of_superset := by
    sorry
  inter_sets := by
    sorry


-- `⌘`


-- the `atTop` filter
-- **ToDo**
example : Filter ℕ where
  sets := {A | ∃ n : ℕ, ∀ a : ℕ, n ≤ a → a ∈ A}
  univ_sets := by
    sorry
  sets_of_superset := by
    sorry
  inter_sets := by
    sorry

#print Filter.atTop
#check atTop
#print Filter.mem_atTop


-- The neighbourhoods of a point in `ℝ`
-- **ToDo**
example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A}
  univ_sets := by
    sorry
  sets_of_superset h h' := by
    sorry
  inter_sets h h' := by
    sorry



-- # § Exercises


-- If `s : Set α`, the set of sets containing `s` is a filter.
-- **Exercise**
example (s : Set α) : Filter α where
  sets := {A : Set α | s ⊆ A}
  univ_sets := sorry
  sets_of_superset h h' := sorry
  inter_sets h h' := sorry


-- Many results about `𝓟` have names containing `principal`.

-- **Exercise**
example (s t : Set α) : t ∈ 𝓟 s ↔ s ⊆ t := sorry

-- **Exercise**
example (s t X : Set α) (hst : t ⊆ s) : X ∈ 𝓟 s → X ∈ 𝓟 t := by
  sorry


-- Define the `atBot` filter: it can be easier to use the definition `Set.Iic a = (-∞ , a]`.
-- **Exercise**
example : Filter ℤ where
  sets := {A | ∃ n, Set.Iic n ⊆ A}
  univ_sets := by
    sorry
  sets_of_superset h h' := by
    sorry
  inter_sets := by
    sorry



/- If `a : ℝ`, we can also look at the collection of subsets of `ℝ` that contain an
interval `(a-ε,a]` with `ε > 0`, and this is still a filter. This open-closed interval
`(a -ε, a]` is called `Set.Ioc (a - ε) a`.
**Exercise** -/
def nhds_left (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Ioc (a - ε) a ⊆ A}
  univ_sets := by
    sorry
  sets_of_superset h h' := by
    sorry
  inter_sets h h' := by
    sorry


-- `⌘`

section ConvergenceOne

-- ## Convergence: Take 1


-- **ToDo**
def Tendsto_preimage (f : α → β) (F : Filter α) (G : Filter β) : Prop :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

-- The behaviour of preimages through composition of functions
#check Set.preimage_comp

-- Compatibility with composition.
-- **ToDo**
example {γ : Type*} (f : α → β) (g : β → γ) (F : Filter α) (G : Filter β) (H : Filter γ) :
    Tendsto_preimage f F G → Tendsto_preimage g G H → Tendsto_preimage (g ∘ f) F H := by
  sorry



-- Link with the "classical" notion
-- **ToDo**
example (f : ℝ → ℝ) (a b : ℝ) : Tendsto_preimage f (𝓝 a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Ioo (a - δ) (a + δ) →
    f x ∈ Ioo (b - ε) (b + ε) := by
  sorry

-- # § Exercise

-- **Exercise**
example (u : ℕ → ℝ) (x₀ : ℝ) : Tendsto_preimage u atTop (𝓝 x₀) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  sorry



-- `⌘`

end ConvergenceOne

-- ## Convergence: Take 2

section ConvergenceTwo

-- The order on filters generalises the one on sets
-- **ToDo**
example (s t : Set α) : s ⊆ t ↔ (𝓟 t).sets ⊆ (𝓟 s).sets := by
  sorry


#print Filter.map

-- A function extends to set in a way compatible to its extension to sets.
-- **ToDo**
example {s : Set α} (f : α → β) : (𝓟 s).map f = 𝓟 (f '' s) := by
  sorry


-- This is in of course in the library, but it is an
-- **Exercise** for you (as the library proof is incomprehensible).
theorem mapMono {α β : Type*} (f : α  → β) : Monotone (map f) := by
  sorry


-- **ToDo**
example : Tendsto (fun (x : ℝ) ↦ x) atTop atTop := by
  sorry


-- **ToDo** Composition becomes much easier!
example {γ : Type*} (f : α → β) (g : β → γ) (F : Filter α) (G : Filter β) (H : Filter γ) :
    Tendsto f F G → Tendsto g G H → Tendsto (g ∘ f) F H := by
  sorry


-- `⌘`


-- # § Exercises


-- **Exercise**
example (F : Filter α) (s : Set α) : 𝓟 s ≤ F ↔ ∀ A ∈ F, s ⊆ A := by
  sorry


-- **Exercise**
example (F : Filter α) (s : Set α) : F ≤ 𝓟 s ↔ s ∈ F := by
  sorry

/- Now to prove the compatibility of limits with compositions,
we use the properties of `Filter.map`.-/
#print Filter.map_map -- `Filter.map (g ∘ f) = Filter.map g ∘ Filter.map f`
-- **Exercise**
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (F : Filter X)
    (G : Filter Y) (H : Filter Z) :
    Tendsto f F G → Tendsto g G H → Tendsto (g ∘ f) F H := by
  sorry


#print Tendsto_preimage
#print Tendsto

-- **Exercise**
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ Tendsto_preimage f F G := sorry



#check mem_nhds_iff_exists_Ioo_subset (α := ℝ)

-- **Exercise** -- do not forget the tactic `linarith` to close easy inequalities
example : Tendsto (fun (x : ℝ) ↦ 1/ x ) atTop (𝓝 0) := by
  sorry



  -- -- filter_upwards

-- `⌘`

end ConvergenceTwo

-- # Filters and eventually true properties.

-- ## `∀ᶠ`


section Eventually


-- **ToDo**
example : atTop.Eventually (fun n : ℕ ↦ 2 ≤ n) := by -- ∀ᶠ n in atTop (α := ℕ), 2 ≤ n
  sorry


-- **ToDo** The "cofinite" filter: properties that are true "for almost every `x`"
example : Filter ℕ where
  sets := {s | Finite ↑(sᶜ)}
  univ_sets := by
    sorry
  sets_of_superset := by
    sorry
  inter_sets := by
    sorry

#check Filter.cofinite
#print Filter.mem_cofinite

#check Nat.Prime.eq_two_or_odd'

-- **ToDo**
example : ∀ᶠ n in Filter.cofinite (α := ℕ), Prime n → Odd n := by
  sorry


-- **Exercise** → This is used in the proof below!
lemma EventuallyLTOne : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 := by
  sorry


-- **ToDo** **WARNING: THIS IS AN UGLY PROOF**
example : ∀ᶠ z in 𝓝 (0 : ℝ), Tendsto (fun (n : ℕ) ↦ z ^ n) atTop (𝓝 0) := by
  sorry


--  **ToDo** : something about `[=]ᶠ`.
example : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) / n) atTop (𝓝 1) := by
  sorry


-- `⌘`


-- # § Exercises


-- **Exercise**
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  sorry


-- **Exercise**
example (p : ℝ → Prop) : ∀ᶠ x in atTop, p x → ∀ᶠ in Filter.cofinite, p x := by
  sorry


/- An **Exercise**: if the sequence `u` converges to `x` and `u n` is in `M` for `n` big enough,
then `x` is in the closure of `M`: a couple of useful lemmas, before:. -/
#check mem_closure_iff_clusterPt
#print ClusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
  sorry


-- **Exercise**
example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := by
  sorry


-- **Exercise**
example (f g : ℝ → ℝ) (x y : ℝ) (h_eq : f =ᶠ[𝓝 x] g) (h_lim : Tendsto f (𝓝 x) (𝓝 y)) :
    Tendsto g (𝓝 x) (𝓝 y) := by
  sorry


end Eventually

-- `⌘`


-- ## `∃ᶠ`

section Frequently

#print Filter.Frequently

-- **ToDo**
example (p : α → Prop) (F : Filter α) : (∃ᶠ x in F, p x) ↔ ∀ A ∈ F, ∃ x ∈ A, p x := by
  sorry

/- There are rationals of the form `1/n` that are arbitrarily close to `0`.
**ToDo** -/
example : ∃ᶠ x in 𝓝 (0 : ℝ), ∃ n : ℤ, x = 1 / (n : ℝ) := by
  sorry


open Polynomial in
/- **ToDo** Recall that a real number is `Algebraic` (over `ℚ`) if it is the root of a
polynomial with rational coeffficients.-/
example : ∃ᶠ (x : ℝ) in atTop, IsAlgebraic ℚ x := by
  sorry



-- **Exercise**
example : ∃ᶠ (n : ℕ) in atTop, Even n := by
  sorry


-- **Exercise**
example (p : ℕ → Prop) (H : ∃ᶠ n in atTop, p (7 * n)) : ∃ᶠ n in atTop, p n := by
  sorry


-- **Exercise**
example : ∃ᶠ n in atTop, Nat.Prime n := by
  sorry


-- **Exercise**
example (p : ℝ → Prop) (h : ∀ᶠ x in atTop, p x) : ∃ᶠ x in atTop, p x := by
  sorry

-- **Exercise** : Why the same proof as above does not generalise? How to fix this?
example (p : α → Prop) (F : Filter α) (h : ∀ᶠ x in F, p x) : ∃ᶠ x in F, p x := by
  sorry

end Frequently
