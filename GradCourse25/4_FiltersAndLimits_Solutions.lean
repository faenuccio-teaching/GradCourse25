import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
-- import Mathlib.Analysis.Calculus.LHopital
-- import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
-- import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

open Set Topology Filter Classical Real

open scoped Filter

section Filters

#print Filter

variable {α β : Type*}

-- If `a : α`, the set of sets containing `a` is a filter
-- **ToDo**
example (a : α) : Filter α where
  sets := {A | a ∈ A}
  univ_sets := mem_univ a
  sets_of_superset := by
    intro S T hS hT
    apply hT.trans
    · rfl
    · exact hS
  inter_sets := by
    intro S T hS hT
    exact ⟨hS, hT⟩


-- `⌘`


-- the `atTop` filter
-- **ToDo**
example : Filter ℕ where
  sets := {A | ∃ n : ℕ, ∀ a : ℕ, n ≤ a → a ∈ A}
  univ_sets := by
    use 0
    intro a
    tauto
  sets_of_superset := by
    intro F G hF hFG
    obtain ⟨n, hn⟩ := hF
    use n
    intro a ha
    apply hFG.trans (by rfl)
    exact hn a ha
  inter_sets := by
    intro S T ⟨n, hn⟩ ⟨m, hm⟩
    use max n m
    intro a ha
    simp only [sup_le_iff] at ha
    exact ⟨hn a ha.1, hm a ha.2⟩

#print Filter.atTop
#check atTop
#print Filter.mem_atTop


-- The neighbourhoods of a point in `ℝ`
-- **ToDo**
example (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Set.Ioo (a - ε) (a + ε) ⊆ A}
  univ_sets := by
    use 1, zero_lt_one, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    use ε, hpos, subset_trans h h'
  inter_sets h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    obtain ⟨ε', hpos', h'⟩ := h'
    use min ε ε', lt_min_iff.mpr ⟨hpos, hpos'⟩
    intro z hz
    apply (inter_subset_inter h h')
    rw [Ioo_inter_Ioo]
    change z ∈ Ioo (max (a - ε) (a - ε')) (min (a + ε) (a + ε'))
    rw [max_sub_sub_left a ε ε', min_add_add_left a ε ε']
    exact hz



-- # § Exercises


-- If `s : Set α`, the set of sets containing `s` is a filter.
-- **Exercise**
example (s : Set α) : Filter α where
  sets := {A : Set α | s ⊆ A}
  univ_sets := subset_univ s
  sets_of_superset h h' := subset_trans h h'
  inter_sets h h' := subset_inter h h'


-- Many results about `𝓟` have names containing `principal`.

-- **Exercise**
example (s t : Set α) : t ∈ 𝓟 s ↔ s ⊆ t := mem_principal

-- **Exercise**
example (s t X : Set α) (hst : t ⊆ s) : X ∈ 𝓟 s → X ∈ 𝓟 t := by
  intro h
  rw [mem_principal] at h ⊢
  exact hst.trans h


-- Define the `atBot` filter: it can be easier to use the definition `Set.Iic a = (-∞ , a]`.
-- **Exercise**
example : Filter ℤ where
  sets := {A | ∃ n, Set.Iic n ⊆ A}
  univ_sets := by
    use 0, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨n, hn⟩ := h
    use n, fun _ hx ↦ (subset_trans hn h') hx
  inter_sets := by
    intro A B hA hB
    obtain ⟨n, hn⟩ := hA
    obtain ⟨m, hm⟩ := hB
    simp only [mem_setOf_eq, subset_inter_iff]
    use min n m
    constructor
    · apply subset_trans _ hn
      exact (Iic_inter_Iic (a := n) (b := m)).symm ▸ inter_subset_left
    · exact subset_trans (Iic_inter_Iic (a := n) (b := m)|>.symm ▸ inter_subset_right) hm



/- If `a : ℝ`, we can also look at the collection of subsets of `ℝ` that contain an
interval `(a-ε,a]` with `ε > 0`, and this is still a filter. This open-closed interval
`(a -ε, a]` is called `Set.Ioc (a - ε) a`.
**Exercise** -/
def nhds_left (a : ℝ) : Filter ℝ where
  sets := {A | ∃ ε > 0, Ioc (a - ε) a ⊆ A}
  univ_sets := by
    use 1, zero_lt_one, subset_univ _
  sets_of_superset h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    use ε, hpos, subset_trans h h'
  inter_sets h h' := by
    obtain ⟨ε, hpos, h⟩ := h
    obtain ⟨ε', hpos', h'⟩ := h'
    use min ε ε', lt_min_iff.mpr ⟨hpos, hpos'⟩
    intro z hz
    apply (inter_subset_inter h h')
    rw [Ioc_inter_Ioc]
    change z ∈ Ioc (max (a - ε) (a - ε')) (min a a)
    rw [max_sub_sub_left a ε ε', min_self]
    exact hz


-- `⌘`


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
  intro h h' U hU
  rw [preimage_comp]
  apply h
  apply h'
  exact hU



-- Link with the "classical" notion
-- **ToDo**
example (f : ℝ → ℝ) (a b : ℝ) : Tendsto_preimage f (𝓝 a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Ioo (a - δ) (a + δ) →
    f x ∈ Ioo (b - ε) (b + ε) := by
  constructor
  · intro H ε ε_pos
    -- rw [Tendsto_preimage] at H
    have hVb : Ioo (b - ε) (b + ε) ∈ 𝓝 b := by
      apply Ioo_mem_nhds <;> linarith
    specialize H _ hVb
    rw [Metric.mem_nhds_iff] at H
    obtain ⟨δ, δ_pos, h_incl⟩ := H
    refine ⟨δ, δ_pos, ?_⟩
    simp only [Ioo_eq_ball, sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel] at h_incl ⊢
    apply h_incl
  · intro H
    -- rw [Tendsto_preimage]
    intro V hV
    rw [Metric.mem_nhds_iff] at hV ⊢
    obtain ⟨ε, ε_pos, hε⟩ := hV
    obtain ⟨δ, δ_pos, h_incl⟩ := H ε ε_pos
    simp only [Ioo_eq_ball, sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel] at h_incl
    refine ⟨δ, δ_pos, ?_⟩
    rw [← image_subset_iff]
    apply subset_trans _ hε
    rw [image_subset_iff]
    exact h_incl

-- # § Exercise

-- **Exercise**
example (u : ℕ → ℝ) (x₀ : ℝ) : Tendsto_preimage u atTop (𝓝 x₀) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  constructor
  · intro H ε ε_pos
    have hVb : Ioo (x₀ - ε) (x₀ + ε) ∈ 𝓝 x₀ := by
      apply Ioo_mem_nhds <;> linarith
    specialize H _ hVb
    rwa [mem_atTop_sets] at H
  · intro H
    intro V hV
    rw [mem_atTop_sets]
    rw [Metric.mem_nhds_iff] at hV
    obtain ⟨ε, ε_pos, hε⟩ := hV
    obtain ⟨N, hN⟩ := H ε ε_pos
    use N
    simp only [Ioo_eq_ball, sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel] at hN
    exact fun n hn ↦ hε <| hN n hn



-- `⌘`



-- ## Convergence: Take 2


-- The order on filters generalises the one on sets
-- **ToDo**
example (s t : Set α) : s ⊆ t ↔ (𝓟 t).sets ⊆ (𝓟 s).sets := by
  constructor
  · exact fun h _ hA ↦ le_trans h hA
  · exact fun h ↦ h (mem_principal_self t)


#print Filter.map

-- A function extends to set in a way compatible to its extension to sets.
-- **ToDo**
example {s : Set α} (f : α → β) : (𝓟 s).map f = 𝓟 (f '' s) := by
  ext A
  change f ⁻¹'A ∈ 𝓟 s ↔ A ∈ 𝓟 (f '' s)
  rw [mem_principal, mem_principal]
  exact Set.image_subset_iff.symm


-- This is in of course in the library, but it is an
-- **Exercise** for you (as the library proof is incomprehensible).
theorem mapMono {α β : Type*} (f : α  → β) : Monotone (map f) := by
  rw [Monotone]
  intro F G h
  rw [Filter.le_def]
  intro S hS
  rw [mem_map] at hS ⊢
  apply h
  assumption


-- **ToDo**
example : Tendsto (fun (x : ℝ) ↦ x) atTop atTop := by
  rw [Tendsto]
  rw [map_id']


-- **ToDo** Composition becomes much easier!
example {γ : Type*} (f : α → β) (g : β → γ) (F : Filter α) (G : Filter β) (H : Filter γ) :
    Tendsto f F G → Tendsto g G H → Tendsto (g ∘ f) F H := by
  intro hFG hGH
  -- rw [Tendsto] at hFG hGH ⊢
  -- have := map_mono (m := g) hFG
  exact_mod_cast le_trans (map_mono /- (m := g) -/ hFG) hGH
  -- apply le_trans (map_mono /- (m := g) -/ hFG) hGH


-- `⌘`


-- # § Exercises


-- **Exercise**
example (F : Filter α) (s : Set α) : 𝓟 s ≤ F ↔ ∀ A ∈ F, s ⊆ A := by
  constructor
  · exact fun h _ hA ↦ h hA
  · exact fun h A hA ↦ h A hA


-- **Exercise**
example (F : Filter α) (s : Set α) : F ≤ 𝓟 s ↔ s ∈ F := by
  constructor
  · exact fun h ↦ h (mem_principal_self s)
  · exact fun h _ hA ↦ F.sets_of_superset h hA

/- Now to prove the compatibility of limits with compositions,
we use the properties of `Filter.map`.-/
#print Filter.map_map -- `Filter.map (g ∘ f) = Filter.map g ∘ Filter.map f`
-- **Exercise**
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (F : Filter X)
    (G : Filter Y) (H : Filter Z) :
    Tendsto f F G → Tendsto g G H → Tendsto (g ∘ f) F H := by
  intro h h'
  change map (g ∘ f) F ≤ H
  rw [← map_map]
  refine le_trans ?_ h'
  apply mapMono -- or `apply map_mono` from the library
  exact h


#print Tendsto_preimage
#print Tendsto

-- **Exercise**
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ Tendsto_preimage f F G := Iff.rfl



#check mem_nhds_iff_exists_Ioo_subset (α := ℝ)

-- **Exercise** -- do not forget the tactic `linarith` to close easy inequalities
example : Tendsto (fun (x : ℝ) ↦ 1/ x ) atTop (𝓝 0) := by
  rw [Tendsto]
  simp only [one_div, Filter.map_inv]--, inv_atTop₀]
  rw [le_def]
  intro s Hs
  rw [Filter.mem_inv, mem_atTop_sets, inv_preimage]
  rw [mem_nhds_iff_exists_Ioo_subset] at Hs
  obtain ⟨m, M, z_mem, hs⟩ := Hs
  use 1 + M⁻¹
  intro x hx
  rw [Set.mem_inv]
  apply hs
  rw [mem_Ioo] at z_mem ⊢
  constructor
  · apply lt_trans z_mem.1
    apply inv_pos_of_pos
    apply lt_of_lt_of_le (inv_pos_of_pos z_mem.2)
    linarith
  · rw [inv_lt_comm₀ _ z_mem.2]
    linarith
    apply lt_of_lt_of_le (inv_pos_of_pos z_mem.2)
    linarith



  -- -- filter_upwards

-- `⌘`


-- # Filters and eventually true properties.

-- ## `∀ᶠ`


-- **ToDo**
example : atTop.Eventually (fun n : ℕ ↦ 2 ≤ n) := by -- ∀ᶠ n in atTop (α := ℕ), 2 ≤ n
  dsimp [Filter.Eventually]
  simp only [mem_atTop_sets, ge_iff_le, mem_setOf_eq]
  use 2
  simp


-- **ToDo** The "cofinite" filter: properties that are true "for almost every `x`"
example : Filter ℕ where
  sets := {s | Finite ↑(sᶜ)}
  univ_sets := by
    simpa only [mem_setOf_eq, compl_univ] using Finite.of_subsingleton
  sets_of_superset := by
    intro s t hs hst
    apply Finite.subset hs
    rwa [compl_subset_compl]
  inter_sets := by
    intro s t hs ht
    simp only [mem_setOf_eq]
    rw [compl_inter]
    apply (finite_union).mpr
    exact ⟨hs, ht⟩

#check Filter.cofinite
#print Filter.mem_cofinite

#check Nat.Prime.eq_two_or_odd'

-- **ToDo**
example : ∀ᶠ n in Filter.cofinite (α := ℕ), Prime n → Odd n := by
  simp only [eventually_cofinite, Classical.not_imp, Nat.not_odd_iff_even]
  rw [finite_iff_bddAbove]
  simp only [bddAbove_def, mem_setOf_eq, and_imp]
  use 2
  -- apply this
  intro p hp hp₂
  rw [← Nat.prime_iff] at hp
  have := Nat.Prime.eq_two_or_odd' hp
  cases this
  · apply le_of_eq
    assumption
  · rw [← Nat.not_odd_iff_even] at hp₂
    tauto


-- **Exercise** → This is used in the proof below!
lemma EventuallyLTOne : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 := by
  rw [Filter.eventually_iff]
  rw [mem_nhds_iff]
  use Ioo (-1 : ℝ) (1 : ℝ)
  refine ⟨?_, isOpen_Ioo, by aesop⟩
  · apply subset_of_eq
    simp only [mem_setOf_eq, abs_lt]
    rfl


-- **ToDo** **WARNING: THIS IS AN UGLY PROOF**
example : ∀ᶠ z in 𝓝 (0 : ℝ), Tendsto (fun (n : ℕ) ↦ z ^ n) atTop (𝓝 0) := by
  have := EventuallyLTOne
  rw [eventually_iff] at this ⊢
  apply Filter.mem_of_superset this
  intro x hx
  simp only [tendsto_pow_atTop_nhds_zero_iff, mem_setOf_eq]
  exact hx


--  **ToDo** Bisogna intrdurre `[=]ᶠ`.
/- E' completamente sbagliato come esempio perche' usa `∀ᶠ` e `[=]ᶠ` e
non usa la definizione di `Tendsto` con `≤`. Si puo' tenere solo se si cambia la
dimostrazione molto, oppure va cambiato esempio. E poi va aggiunto un ex simile
a questo.-/
example : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) / n) atTop (𝓝 1) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat 1
  have h2 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h3 := Tendsto.add h1 h2
  rw [zero_add] at h3
  rw [Tendsto]
  -- refine Tendsto.congr' ?_ h3
  apply le_trans (le_of_eq ?_) h3
  congr
  ext -- this is false, but eventually true
  sorry
  -- rw [Filter.EventuallyEq]
  -- filter_upwards [eventually_ne_atTop 0] with n hn
  -- rw [Filter.Eventually]
  -- rw [Filter.mem_atTop_sets]
  -- use 1
  -- intro n hn
  -- simp only [one_div, mem_setOf_eq]
  -- rw [add_div, div_self]
  -- · ring
  -- · rw [Nat.cast_ne_zero]
  --   omega


-- `⌘`


-- # § Exercises


-- **Exercise**
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  dsimp [Filter.Eventually] at hP hQ ⊢
  exact atTop.inter_sets hP hQ


-- **Exercise**
example (p : ℝ → Prop) : ∀ᶠ x in atTop, p x → ∀ᶠ in Filter.cofinite, p x := by
  exact Filter.Eventually.of_forall fun x a ↦ a


/- An **Exercise**: if the sequence `u` converges to `x` and `u n` is in `M` for `n` big enough,
then `x` is in the closure of `M`: a couple of useful lemmas, before:. -/
#check mem_closure_iff_clusterPt
#print ClusterPt
#check le_principal_iff
#check neBot_of_le
example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  change (𝓝 x ⊓ 𝓟 M).NeBot
  apply neBot_of_le (f := map u atTop)
  rw [le_inf_iff]
  refine ⟨hux, ?_⟩
  refine le_trans (map_mono (m := u) (le_principal_iff.mpr huM)) ?_
  simp only [map_principal, le_principal_iff, mem_principal, image_subset_iff]
  intro x
  simp


-- **Exercise**
example : ∀ᶠ x in nhds (0 : ℝ), |x| ≤ 1/2 := by
  dsimp [Filter.Eventually]
  rw [(nhds_basis_Ioo_pos 0).mem_iff]
  use 1/2
  constructor
  · simp only [one_div, inv_pos, Nat.ofNat_pos]
  · simp only [zero_sub, zero_add]
    intro x ⟨hx₁, hx₂⟩
    rw [mem_setOf_eq, abs_le]
    exact ⟨le_of_lt hx₁, le_of_lt hx₂⟩



-- `⌘`

-- ## `∃ᶠ`

#print Filter.Frequently
-- `Filter.Frequently p F` means `¬∀ᶠ (x : α) in f, ¬p x` i.e.
-- `{x | ¬p x} ∉ F`. It is written `∃ᶠ x in F, p x`.
-- This is actually equivalent to saying that, for every `A ∈ F`,
-- there exists `x ∈ A` such that `p x`. Don't believe me?


/- There are rationals of the form `1/n` that are arbitrarily close to `0`.
**ToDo** -/
example : ∃ᶠ x in 𝓝 (0 : ℝ), ∃ n : ℤ, x = 1 / (n : ℝ) := by
  rw [frequently_nhds_iff]
  intro U hU_mem hU_open
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨ε, ε_pos, hε⟩ := hU_open 0 hU_mem
  set L := Nat.ceil ε⁻¹ + 1 with hL₀
  have hL : (L : ℝ)⁻¹ < ε := by
    rw [hL₀]
    rw [inv_lt_iff_one_lt_mul₀, Nat.cast_add, mul_add, Nat.cast_one, mul_one, ← sub_lt_iff_lt_add]
    · calc 1 - ε < 1 := by simp_all
      _ = ε * ε⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt ε_pos)]
      _ ≤ ε * (⌈ ε⁻¹ ⌉₊ : ℝ) := by
        rw [mul_le_mul_iff_of_pos_left (ε_pos)]
        exact Nat.le_ceil ε⁻¹
    · norm_cast
      omega
  use (L : ℝ)⁻¹
  constructor
  · apply hε
    simpa
  · use L
    simp



-- Of course, this result is already in mathlib:
-- **Exercise**
theorem frequently_iff' {f : Filter α} {P : α → Prop} :
    (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x := by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _)]
  rfl


-- **Exercise**
example (p : ℕ → Prop) (H : ∃ᶠ n in atTop, p (7 * n)) : ∃ᶠ n in atTop, p n := by
  rw [frequently_atTop] at H
  -- replace H := H n
  rw [frequently_atTop]
  intro n
  replace H := H n
  obtain ⟨b, ⟨hb1, hb2⟩⟩ := H
  use 7*b
  constructor
  · omega
  · assumption


-- **Exercise**
example : ∃ᶠ n in atTop, Nat.Prime n := by
  rw [frequently_atTop]
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  use p

-- **ToDo**
example (p : α → Prop) (F : Filter α) : (∃ᶠ x in F, p x) ↔ ∀ A ∈ F, ∃ x ∈ A, p x := by
  constructor
  · intro h A hA
    by_contra habs
    push_neg at habs
    have hsub : A ⊆ {x | ¬p x} := by
      intro x hx
      simp only [mem_setOf_eq, habs x hx, not_false_eq_true]
    have := F.mem_of_superset hA hsub
    exact h this
  · dsimp [Filter.Frequently]
    intro h habs
    obtain ⟨x, hx₁, hx₂⟩ := h _ habs
    simp only [mem_setOf_eq] at hx₁
    exact hx₁ hx₂

end Filters
