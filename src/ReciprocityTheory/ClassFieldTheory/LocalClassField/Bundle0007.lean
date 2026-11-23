module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0005
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.Bundle0011
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.KbarRepContAction
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0006
public import ReciprocityTheory.GroupCohomology.Bundle0007
public import ReciprocityTheory.GroupCohomology.Shapiro

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

open Topology
open scoped commutatorElement

variable {p K L}

theorem IsAbLK.normal (h : IsAbLK p K L) : (subG p K L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [h1]
  exact mul_mem (h.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn

theorem isAbLK_self (hK : FiniteDimensional ℚ_[p] K) : IsAbLK p K K :=
  ⟨le_rfl, hK, fun σ _ x hx => σ.commutes ⟨x, hx⟩⟩

theorem subG_sup_eq_inf (L L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    subG p K (L ⊔ L') = subG p K L ⊓ subG p K L' := by
  refine le_antisymm (le_inf (subG_anti le_sup_left) (subG_anti le_sup_right)) fun σ hσ => ?_
  have hle : L ⊔ L' ≤ (IntermediateField.fixedField (Subgroup.zpowers σ)).restrictScalars ℚ_[p] := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.1 : Subgroup.zpowers σ ≤ subG p K L) hτ x hx
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.2 : Subgroup.zpowers σ ≤ subG p K L') hτ x hx
  intro x hx
  have := hle hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.mem_zpowers σ)

theorem IsAbLK.sup {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : IsAbLK p K L) (h' : IsAbLK p K L') : IsAbLK p K (L ⊔ L') := by
  refine ⟨h.le.trans le_sup_left, ?_, ?_⟩
  · have := h.fin
    have := h'.fin
    exact IntermediateField.finiteDimensional_sup L L'
  · rw [subG_sup_eq_inf]
    exact le_inf h.comm h'.comm

theorem IsAbLK.of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h' : IsAbLK p K L') (hK : K ≤ L) (hL : L ≤ L') : IsAbLK p K L := by
  refine ⟨hK, ?_, h'.comm.trans (subG_anti hL)⟩
  have := h'.fin
  exact Module.Finite.of_injective (IntermediateField.inclusion hL).toLinearMap
    (IntermediateField.inclusion hL).injective

theorem isAbLK_of_cyclic (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : IsAbLK p K L := by
  refine ⟨h, hL, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 ⟨⟨fun a b => ?_⟩⟩⟩
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hg b
  exact (zpow_mul_comm g₀ i j)

theorem isAbLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : IsAbLK p K (Kn p K n) := by
  letI : (subG p K (Kn p K n)).Normal :=
    subG_normal_of_stable (Kn_stable p K n)
  exact isAbLK_of_cyclic (finiteDimensional_Kn p K hK hn) (le_Kn p K n)
    (frobLK p K (Kn p K n)) (by
      intro g
      obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn
        ((isFrob_frobK hK).isFrobOn n) σ
      refine ⟨i, ?_⟩
      change frobLK p K (Kn p K n) ^ (i : ℤ) = _
      rw [zpow_natCast, frobLK_pow]
      exact ((mk_eq_mk_iff _ _).2 hi).symm)

theorem toAbK_surjective : Surjective (toAbK p K) := QuotientGroup.mk'_surjective _

theorem continuous_toAbK : Continuous (toAbK p K) := QuotientGroup.continuous_mk

theorem isOpenMap_toAbK : IsOpenMap (toAbK p K) := QuotientGroup.isOpenMap_coe

theorem mem_closure_commutator_iff (hK : FiniteDimensional ℚ_[p] K) (g : GK p K) :
    g ∈ (commutator (GK p K)).topologicalClosure ↔ ∀ L, IsAbLK p K L → g ∈ subG p K L := by
  constructor
  · intro hg L hL
    exact Subgroup.topologicalClosure_minimal _ hL.comm (isClosed_subG p K L) hg
  · intro hg
    obtain ⟨M, hM, hMe⟩ := exists_subG_eq (commutator (GK p K)).topologicalClosure
      (Subgroup.isClosed_topologicalClosure _)
    rw [← hMe]
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hle : K ⊔ IntermediateField.adjoin ℚ_[p] {x} ≤ M :=
      sup_le hM (IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hx))
    have hab : IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {x}) := by
      refine ⟨le_sup_left, IntermediateField.finiteDimensional_sup _ _, ?_⟩
      refine le_trans ?_ (subG_anti hle)
      rw [hMe]
      exact Subgroup.le_topologicalClosure _
    exact hg _ hab x (le_sup_right (a := K) (IntermediateField.mem_adjoin_simple_self ℚ_[p] x))

theorem toAbK_eq_iff (hK : FiniteDimensional ℚ_[p] K) (g g' : GK p K) :
    toAbK p K g = toAbK p K g' ↔ ∀ L, IsAbLK p K L → g⁻¹ * g' ∈ subG p K L := by
  rw [← mem_closure_commutator_iff hK]
  exact QuotientGroup.eq

theorem exists_of_compatible (hK : FiniteDimensional ℚ_[p] K) (γ : IntermediateField ℚ_[p] (PadicAlgCl p) → GK p K)
    (hγ : ∀ L L', IsAbLK p K L → IsAbLK p K L' → L ≤ L' → (γ L)⁻¹ * γ L' ∈ subG p K L) :
    ∃ g : GK p K, ∀ L, IsAbLK p K L → (γ L)⁻¹ * g ∈ subG p K L := by
  have : Nonempty {L // IsAbLK p K L} := ⟨⟨K, isAbLK_self hK⟩⟩
  let t : {L // IsAbLK p K L} → Set (GK p K) := fun L => {g | (γ L.1)⁻¹ * g ∈ subG p K L.1}
  have hcl : ∀ i, IsClosed (t i) := fun i =>
    (isClosed_subG p K i.1).preimage (continuous_const.mul continuous_id)
  have hmono : ∀ i j : {L // IsAbLK p K L}, i.1 ≤ j.1 → t j ⊆ t i := fun i j hij g hg => by
    have h1 : (γ i.1)⁻¹ * g = ((γ i.1)⁻¹ * γ j.1) * ((γ j.1)⁻¹ * g) := by group
    show (γ i.1)⁻¹ * g ∈ subG p K i.1
    rw [h1]
    exact mul_mem (hγ _ _ i.2 j.2 hij) (subG_anti hij hg)
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩, hmono _ _ le_sup_left, hmono _ _ le_sup_right⟩)
    (fun i => ⟨γ i.1, by show (γ i.1)⁻¹ * γ i.1 ∈ subG p K i.1; rw [inv_mul_cancel]; exact one_mem _⟩)
    (fun i => (hcl i).isCompact) hcl
  exact ⟨g, fun L hL => Set.mem_iInter.1 hg ⟨L, hL⟩⟩

theorem exists_subG_subset (hK : FiniteDimensional ℚ_[p] K) (O : Set (GK p K)) (hO : IsOpen O)
    (h : ((commutator (GK p K)).topologicalClosure : Set (GK p K)) ⊆ O) :
    ∃ L, IsAbLK p K L ∧ (subG p K L : Set (GK p K)) ⊆ O := by
  have : Nonempty {L // IsAbLK p K L} := ⟨⟨K, isAbLK_self hK⟩⟩
  obtain ⟨i, hi⟩ := (hO.isClosed_compl.isCompact.elim_directed_family_closed
    (fun L : {L // IsAbLK p K L} => (subG p K L.1 : Set (GK p K))) (fun i => isClosed_subG p K i.1)
    (by
      rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
      rintro g ⟨hg1, hg2⟩
      exact hg1 (h ((mem_closure_commutator_iff hK g).2 fun L hL => Set.mem_iInter.1 hg2 ⟨L, hL⟩)))
    (fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩, subG_anti le_sup_left, subG_anti le_sup_right⟩)).imp (fun _ => Disjoint.inter_eq)
  refine ⟨i.1, i.2, fun g hg => ?_⟩
  by_contra hgO
  exact (Set.eq_empty_iff_forall_notMem.1 hi g) ⟨hgO, hg⟩

theorem exists_coset_subset (hK : FiniteDimensional ℚ_[p] K) (g : GK p K) (W : Set (GKab p K))
    (hW : W ∈ 𝓝 (toAbK p K g)) :
    ∃ L, IsAbLK p K L ∧ ∀ g' : GK p K, g⁻¹ * g' ∈ subG p K L → toAbK p K g' ∈ W := by
  obtain ⟨V, hVW, hV, hgV⟩ := mem_nhds_iff.1 hW
  obtain ⟨L, hL, hsub⟩ := exists_subG_subset hK ((fun h : GK p K => toAbK p K (g * h)) ⁻¹' V)
    (hV.preimage (continuous_toAbK.comp (continuous_const.mul continuous_id))) (fun h hh => by
      show toAbK p K (g * h) ∈ V
      have : toAbK p K (g * h) = toAbK p K g := by
        rw [map_mul, show toAbK p K h = 1 from (QuotientGroup.eq_one_iff h).2 hh, mul_one]
      rw [this]; exact hgV)
  refine ⟨L, hL, fun g' hg' => hVW ?_⟩
  have := hsub hg'
  simpa using this

theorem coset_mem_nhds (hL : IsAbLK p K L) (g : GK p K) :
    toAbK p K '' {g' | g⁻¹ * g' ∈ subG p K L} ∈ 𝓝 (toAbK p K g) := by
  refine (isOpenMap_toAbK _ ?_).mem_nhds ⟨g, ?_, rfl⟩
  · exact (isOpen_subG hL.fin).preimage (continuous_const.mul continuous_id)
  · show g⁻¹ * g ∈ subG p K L
    rw [inv_mul_cancel]; exact one_mem _

theorem continuous_GKab_iff (hK : FiniteDimensional ℚ_[p] K) {X : Type*} [TopologicalSpace X] (f : X → GKab p K) :
    Continuous f ↔ ∀ L, IsAbLK p K L → ∀ x, ∀ᶠ y in 𝓝 x, ∀ g g' : GK p K, toAbK p K g = f x → toAbK p K g' = f y →
      g⁻¹ * g' ∈ subG p K L := by
  constructor
  · intro hf L hL x
    obtain ⟨g₀, hg₀⟩ := toAbK_surjective (f x)
    have hn := coset_mem_nhds hL g₀
    rw [hg₀] at hn
    filter_upwards [hf.continuousAt hn] with y hy g g' hg hg'
    obtain ⟨g₁, hg₁, hg₁y⟩ := hy
    have h1 : g⁻¹ * g₀ ∈ subG p K L := (toAbK_eq_iff hK g g₀).1 (hg.trans hg₀.symm) L hL
    have h2 : g₁⁻¹ * g' ∈ subG p K L := (toAbK_eq_iff hK g₁ g').1 (hg₁y.trans hg'.symm) L hL
    have h3 : g⁻¹ * g' = (g⁻¹ * g₀) * (g₀⁻¹ * g₁) * (g₁⁻¹ * g') := by group
    rw [h3]
    exact mul_mem (mul_mem h1 hg₁) h2
  · intro h
    rw [continuous_iff_continuousAt]
    intro x W hW
    obtain ⟨g₀, hg₀⟩ := toAbK_surjective (f x)
    rw [← hg₀] at hW
    obtain ⟨L, hL, hsub⟩ := exists_coset_subset hK g₀ W hW
    rw [Filter.mem_map]
    filter_upwards [h L hL x] with y hy
    obtain ⟨g₁, hg₁⟩ := toAbK_surjective (f y)
    show f y ∈ W
    rw [← hg₁]
    exact hsub g₁ (hy g₀ g₁ hg₀ hg₁)

theorem denseRange_GKab_iff (hK : FiniteDimensional ℚ_[p] K) {X : Type*} (f : X → GKab p K) :
    DenseRange f ↔ ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : X) (g' : GK p K), toAbK p K g' = f x ∧
      g'⁻¹ * g ∈ subG p K L := by
  constructor
  · intro hf L hL g
    obtain ⟨x, g', hg', hx⟩ := hf.mem_nhds (coset_mem_nhds hL g)
    refine ⟨x, g', hx, ?_⟩
    have : g'⁻¹ * g = (g⁻¹ * g')⁻¹ := by group
    rw [this]
    exact inv_mem hg'
  · intro h y
    obtain ⟨g, rfl⟩ := toAbK_surjective y
    rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨L, hL, hsub⟩ := exists_coset_subset hK g W hW
    obtain ⟨x, g', hg', hx⟩ := h L hL g
    refine ⟨f x, ?_, x, rfl⟩
    rw [← hg']
    refine hsub g' ?_
    have : g⁻¹ * g' = (g'⁻¹ * g)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem exists_hom_GKab (hK : FiniteDimensional ℚ_[p] K) {A : Type*} [Group A] (γ : IntermediateField ℚ_[p] (PadicAlgCl p) → A → GK p K)
    (hmul : ∀ L, IsAbLK p K L → ∀ a b, (γ L (a * b))⁻¹ * (γ L a * γ L b) ∈ subG p K L)
    (hγ : ∀ L L', IsAbLK p K L → IsAbLK p K L' → L ≤ L' → ∀ a, (γ L a)⁻¹ * γ L' a ∈ subG p K L) :
    ∃ f : A →* GKab p K, ∀ L, IsAbLK p K L → ∀ (a : A) (g : GK p K), toAbK p K g = f a →
      (γ L a)⁻¹ * g ∈ subG p K L := by
  have hex : ∀ a, ∃ g : GK p K, ∀ L, IsAbLK p K L → (γ L a)⁻¹ * g ∈ subG p K L := fun a =>
    exists_of_compatible hK (fun L => γ L a) fun L L' hL hL' hle => hγ L L' hL hL' hle a
  choose s hs using hex
  refine ⟨MonoidHom.mk' (fun a => toAbK p K (s a)) fun a b => ?_, fun L hL a g hg => ?_⟩
  · rw [← map_mul, toAbK_eq_iff hK]
    intro L hL
    have := hL.normal
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, ← QuotientGroup.eq.2 (hs a L hL), ← QuotientGroup.eq.2 (hs b L hL),
      ← QuotientGroup.eq.2 (hs (a * b) L hL), ← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.2 (hmul L hL a b)
  · have h1 : (s a)⁻¹ * g ∈ subG p K L := (toAbK_eq_iff hK (s a) g).1 hg.symm L hL
    have h2 : (γ L a)⁻¹ * g = ((γ L a)⁻¹ * s a) * ((s a)⁻¹ * g) := by group
    rw [h2]
    exact mul_mem (hs a L hL) h1

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

theorem exists_units_of_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L))
    (f : H → Lˣ) (E : IntermediateField K L) [FiniteDimensional K E]
    (hE : ∀ h : H, (h : L ≃ₐ[K] L) ∈ E.fixingSubgroup → f h = 1)
    (hc : ∀ g h : H, f (g * h) = f g * Units.map ((g : L ≃ₐ[K] L) : L →* L) (f h)) :
    ∃ β : Lˣ, ∀ h : H, f h = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  classical

  let r : H → (E →ₐ[K] L) := fun h => ((h : L ≃ₐ[K] L) : L →ₐ[K] L).comp E.val
  have hr : ∀ (h : H) (x : E), r h x = (h : L ≃ₐ[K] L) (x : L) := fun _ _ => rfl
  have hfr : ∀ g h : H, r g = r h → f g = f h := by
    intro g h hgh
    have hmem : ((g⁻¹ * h : H) : L ≃ₐ[K] L) ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x := DFunLike.congr_fun hgh ⟨x, hx⟩
      show ((g : L ≃ₐ[K] L)⁻¹ * (h : L ≃ₐ[K] L)) x = x
      rw [AlgEquiv.mul_apply, ← h1]
      exact (g : L ≃ₐ[K] L).symm_apply_apply x
    have h2 := hc g (g⁻¹ * h)
    rw [mul_inv_cancel_left, hE _ hmem, map_one, mul_one] at h2
    exact h2.symm
  let S := Set.range r
  have : Finite (E →ₐ[K] L) := inferInstance
  let _ : Fintype S := Fintype.ofFinite S
  have hrep : ∀ s : S, ∃ h : H, r h = s.1 := fun s => s.2
  choose rep hrep using hrep
  let a : S → L := fun s => (f (rep s) : L)
  have hli : LinearIndependent L (fun s : S => ((s.1 : E →* L) : E → L)) := by
    refine (linearIndependent_monoidHom E L).comp (fun s : S => (s.1 : E →* L)) ?_
    intro s t hst
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hst x
  have hex : ∃ c : E, ∑ s : S, a s * s.1 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ s : S, a s • ((s.1 : E →* L) : E → L) = 0 := by
      funext c
      rw [Finset.sum_apply]
      exact hcon c
    have := Fintype.linearIndependent_iff.1 hli a h0 ⟨r 1, 1, rfl⟩
    exact (f (rep ⟨r 1, 1, rfl⟩)).ne_zero this
  obtain ⟨c, hcne⟩ := hex
  set b : L := ∑ s : S, a s * s.1 c with hb
  have key : ∀ h : H, b = f h * (h : L ≃ₐ[K] L) b := by
    intro h
    let m : S → S := fun s => ⟨r (h * rep s), _, rfl⟩
    have hm1 : ∀ (s : S) (x : E), (m s).1 x = (h : L ≃ₐ[K] L) (s.1 x) := by
      intro s x
      show r (h * rep s) x = _
      rw [← hrep s, hr, hr]
      rfl
    have hminj : Function.Injective m := by
      intro s t hst
      apply Subtype.ext
      apply AlgHom.ext
      intro x
      apply (h : L ≃ₐ[K] L).injective
      rw [← hm1, ← hm1, hst]
    have hmbij : Function.Bijective m := Finite.injective_iff_bijective.1 hminj
    have hma : ∀ s, a (m s) = f h * (h : L ≃ₐ[K] L) (a s) := by
      intro s
      show (f (rep (m s)) : L) = _
      rw [hfr (rep (m s)) (h * rep s) (hrep (m s)), hc]
      rfl
    calc b = ∑ s, a (m s) * (m s).1 c := (hmbij.sum_comp (fun s => a s * s.1 c)).symm
      _ = f h * (h : L ≃ₐ[K] L) b := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hb, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hma, hm1, map_mul, mul_assoc]
  refine ⟨(Units.mk0 b hcne)⁻¹, fun h => ?_⟩
  apply Units.ext
  have hb' : (h : L ≃ₐ[K] L) b ≠ 0 := by
    simpa using hcne
  have e1 : ((Units.map ((h : L ≃ₐ[K] L) : L →* L) (Units.mk0 b hcne)⁻¹ / (Units.mk0 b hcne)⁻¹ : Lˣ) : L)
      = ((h : L ≃ₐ[K] L) b)⁻¹ * b := by
    rw [map_inv, div_inv_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  rw [e1]
  field_simp
  exact (key h).symm

theorem exists_units_of_continuous_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (e : X ≃ Lˣ)
    (f : H → X) (hf : Continuous f)
    (hc : ∀ g h : H, e (f (g * h)) = e (f g) * Units.map ((g : L ≃ₐ[K] L) : L →* L) (e (f h))) :
    ∃ β : Lˣ, ∀ h : H, e (f h) = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  have h1 : e (f 1) = 1 := by
    have h := hc 1 1
    rw [mul_one] at h
    have h' : Units.map (((1 : H) : L ≃ₐ[K] L) : L →* L) (e (f 1)) = e (f 1) := Units.ext rfl
    rw [h'] at h
    exact (left_eq_mul.1 h)
  have hopen : IsOpen (f ⁻¹' {f 1}) := (isOpen_discrete _).preimage hf
  obtain ⟨V, hV, hVf⟩ := isOpen_induced_iff.1 hopen
  have h1V : (1 : L ≃ₐ[K] L) ∈ V := by
    have : (1 : H) ∈ Subtype.val ⁻¹' V := by rw [hVf]; rfl
    exact this
  obtain ⟨E, hfin, hEV⟩ := (krullTopology_mem_nhds_one_iff K L V).1 (hV.mem_nhds h1V)
  refine exists_units_of_cocycle H (fun h => e (f h)) E (fun h hh => ?_) hc
  have : h ∈ Subtype.val ⁻¹' V := hEV hh
  rw [hVf] at this
  have h2 : f h = f 1 := this
  show e (f h) = 1
  rw [h2, h1]

section Padic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem kbar_cocycle_subgroup (H : Subgroup (GK p K)) (f : H → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h : H, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h : H, f h = kbarRep p K h m - m := by
  obtain ⟨β, hβ⟩ := exists_units_of_continuous_cocycle H
    (X := KbarMult p) (Additive.toMul : Additive (PadicAlgCl p)ˣ ≃ (PadicAlgCl p)ˣ) f hf
    (fun g h => congrArg (Additive.toMul : Additive (PadicAlgCl p)ˣ → (PadicAlgCl p)ˣ) (hc g h))
  exact ⟨(Additive.ofMul β : Additive (PadicAlgCl p)ˣ), fun h =>
    congrArg (Additive.ofMul : (PadicAlgCl p)ˣ → Additive (PadicAlgCl p)ˣ) (hβ h)⟩

theorem kbar_cocycle (f : GK p K → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h, f h = kbarRep p K h m - m := by
  obtain ⟨m, hm⟩ := kbar_cocycle_subgroup p K ⊤ (fun h => f h.1) (hf.comp continuous_subtype_val)
    (fun g h => hc g.1 h.1)
  exact ⟨m, fun h => hm ⟨h, Subgroup.mem_top h⟩⟩

theorem h1_kbarRep_subsingleton : Subsingleton (H1 (kbarRep p K)) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  rw [Submodule.mem_comap]
  show z ∈ Bd1 _
  rw [mem_contCoboundaries1]
  exact kbar_cocycle p K z hz.1 hz.2

end Padic

section TRep

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem restricted_multiplicative_h1_subsingleton (H : Subgroup (GK p K)) :
    Subsingleton (((kbarT p K).resSub H).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : ((kbarT p K).resSub H).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : ((kbarT p K).resSub H).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle_subgroup p K H (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]

theorem multiplicative_cochain_h1_subsingleton : Subsingleton ((kbarT p K).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : (kbarT p K).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : (kbarT p K).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle p K (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]

theorem quotient_multiplicative_h1_subsingleton (N : Subgroup (GK p K)) [N.Normal] (Q : TRep ℤ (GK p K ⧸ N))
    (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) : Subsingleton (Q.H 1) :=
  have := multiplicative_cochain_h1_subsingleton p K
  (inf_inj (kbarT p K) N Q P hP).subsingleton

theorem multiplicative_inflation_h2_injective (N : Subgroup (GK p K)) [N.Normal] (hN : IsClosed (N : Set (GK p K)))
    (Q : TRep ℤ (GK p K ⧸ N)) (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) :
    Function.Injective (P.hom.H 2) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have hs := restricted_multiplicative_h1_subsingleton p K N
  obtain ⟨tg, -, hex⟩ := fiveTerm_holds ℤ (GK p K) (kbarT p K) N hN Q P hP ⊤
    (fun x => ⟨fun _ s c _ _ => Subsingleton.elim _ _, fun _ => Submodule.mem_top⟩)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := (hex y).1 hy
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, map_zero]

end TRep

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.SubsingletonHOfSubsingleton
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

theorem pair_bij {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) := by
  refine shp_qi_of_bij P.hom (fun n => ⟨hom_f_injective P hφ.surjective hu.injective n, fun t' => ?_⟩) n
  let eφ := IsHomeomorph.homeomorph _ hφ
  let eu := IsHomeomorph.homeomorph _ hu
  have hc : Continuous fun v : Fin n → G => eu.symm (t'.1 fun i => eφ.symm (v i)) :=
    eu.symm.continuous.comp ((show Continuous t'.1 from t'.2).comp
      (continuous_pi fun i => eφ.symm.continuous.comp (continuous_apply i)))
  refine ⟨⟨_, hc⟩, Subtype.ext (funext fun g => ?_)⟩
  show eu (eu.symm (t'.1 fun i => eφ.symm (eφ (g i)))) = t'.1 g
  rw [eu.apply_symm_apply]
  exact congrArg t'.1 (funext fun i => eφ.symm_apply_apply (g i))

theorem exists_normal_index {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [hl : Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card (α := H)).ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) l (n := j) (by rw [hk]; exact pow_dvd_pow _ (Nat.le_succ j))
  have hidx : K.index = l := by
    have := K.card_mul_index
    rw [hK, hk, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hl.1.pos j) this
  refine ⟨K, Subgroup.normal_of_index_eq_minFac_card ?_, hidx⟩
  rw [hidx, hk, Nat.Prime.pow_minFac hl.1 (Nat.succ_ne_zero j)]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

