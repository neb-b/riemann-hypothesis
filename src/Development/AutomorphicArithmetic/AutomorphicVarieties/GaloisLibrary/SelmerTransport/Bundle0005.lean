module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelDown
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_addMonoidHom_le_of_card_eq {R A B C X : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
    (f : A →ₗ[R] X) (j : B →ₗ[R] X) (hj : Function.Injective j) (g : B →ₗ[R] C)
    (h : ∀ x, g x = 0 → j x ∈ LinearMap.range f) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  have hex : Function.Exact (LinearMap.ker g).subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      have := congrArg Subtype.val hx
      simpa [LinearMap.mem_ker] using this
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simpa using y.2
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict hex]
  gcongr
  · let φ : LinearMap.ker g →ₗ[R] LinearMap.range f :=
      (j.comp (LinearMap.ker g).subtype).codRestrict (LinearMap.range f) (fun x => h x x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply hj
      exact congrArg Subtype.val hab
    calc Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.range f) :=
          Module.length_le_of_injective φ hφ
      _ ≤ Module.length R A := Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  · exact Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)

theorem UpperTheory.V.Base.selDown :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R (selEig ρ U' h𝒟 U 1) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) + Module.length R (resCoker ρ h) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U _ h 𝒟 h𝒟 ι _ D hD hcov
  have hinv : ∀ x : selEig ρ U' h𝒟 U 1,
      ((x : LocSel ρ U' 𝒟) : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' := by
    intro x
    rw [Representation.mem_invariants]
    intro u
    have := (mem_eig.mp x.2) u
    simpa [selRep, Representation.subrepresentation] using congrArg Subtype.val this
  let j : selEig ρ U' h𝒟 U 1 →ₗ[R] H1U ρ U' :=
    (LocSel ρ U' 𝒟).subtype.comp (selEig ρ U' h𝒟 U 1).subtype
  let g : selEig ρ U' h𝒟 U 1 →ₗ[R] resCoker ρ h :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') j hinv)
  let A := Submodule.comap (resU ρ h) (LocSel ρ U' 𝒟)
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hker : ∀ x, g x = 0 → j x ∈ LinearMap.range ((resU ρ h).comp A.subtype) := by
    intro x hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨⟨y, ?_⟩, hy⟩
    show resU ρ h y ∈ LocSel ρ U' 𝒟
    rw [hy]
    exact (x : LocSel ρ U' 𝒟).2
  refine le_trans (length_addMonoidHom_le_of_card_eq ((resU ρ h).comp A.subtype) j hj g hker) ?_
  gcongr
  exact selLocal R G M ρ U' U h 𝒟 ι D hD hcov
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelUnit
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem eq_zero_of_nsmul {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ}
    (hn : IsUnit (n : R)) {x : N} (hx : n • x = 0) : x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R] at hx
  exact (hn.smul_eq_zero).1 hx

theorem UpperTheory.V.Base.selUnit :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      IsUnit (U'.relIndex U : R) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Function.Injective (selRes ρ h 𝒟) ∧ LinearMap.range (selRes ρ h 𝒟) = selEig ρ U' h𝒟 U 1 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hop hu 𝒟 h𝒟
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : resU ρ h x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (eq_zero_of_nsmul hu (kerResSmul R G M ρ U' U h x.1 h0))
  · ext y
    rw [selEig, eig_one]
    constructor
    · rintro ⟨x, rfl⟩ g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    · intro hy
      have hy' : y.1 ∈ invariantsUnderSubgroupH1 ρ U U' := fun g => congrArg Subtype.val (hy g)
      have h1 := corInv R G M ρ hρ U' U h hop y.1 hy'
      rw [← Nat.cast_smul_eq_nsmul R] at h1
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have h2 := Submodule.smul_mem _ v h1
      rw [smul_smul, hv, one_smul] at h2
      obtain ⟨x, hx⟩ := h2
      have hxs : x ∈ LocSel ρ U 𝒟 := by
        rw [mem_locSel]
        intro D hD
        have hu' : IsUnit (((U' ⊓ D).relIndex (U ⊓ D) : ℕ) : R) :=
          isUnit_of_dvd_unit (Nat.cast_dvd_cast (relIndex_inf_dvd U' U D)) hu
        refine eq_zero_of_nsmul hu' (kerResSmul R G M ρ _ _ (inf_le_inf_right D h) _ ?_)
        rw [resU_resU, ← resU_resU ρ inf_le_left h, hx]
        exact mem_locSel.1 y.2 D hD
      exact ⟨⟨x, hxs⟩, Subtype.ext hx⟩
end

