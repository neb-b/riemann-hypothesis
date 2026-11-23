module

public import Mathlib
public import GroundTheory.LocalFields.Bundle0013
public import GroundTheory.LocalFields.Bundle0015
public import GroundTheory.LocalFields.Bundle0017
public import GroundTheory.LocalFields.LocalArtinTransport
public import GroundTheory.LocalFields.LocalArtinBaseChange

@[expose] public section

-- bundled from GroundTheory.LocalFields.ArtinConductorAbelian
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section HasseArf

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]



end HasseArf

section OneDim

variable {G : Type*} [Group G]

def charRep (ψ : G →* ℂˣ) : Representation ℂ G ℂ :=
  (DistribMulAction.toModuleEnd ℂ ℂ).comp ψ

@[simp]
theorem charRep_apply (ψ : G →* ℂˣ) (g : G) (v : ℂ) : charRep ψ g v = (ψ g : ℂ) * v :=
  rfl


end OneDim

section Conductor

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]


end Conductor

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalArtinAbstractField
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

section Embedding

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsSepClosure K Ω] in
theorem isAbelianGalois_fieldRange (ι : L →ₐ[K] Ω) : IsAbelianGalois K ι.fieldRange :=
  have := IsGalois.of_algEquiv ι.equivFieldRange
  { toIsMulCommutative := ⟨⟨fun σ τ => (AlgEquiv.autCongr ι.equivFieldRange).symm.injective
      ((map_mul _ σ τ).trans ((mul_comm' _ _).trans (map_mul _ τ σ).symm))⟩⟩ }

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsAbelianGalois K L]
  [IsSepClosure K Ω] in
theorem finiteDimensional_fieldRange (ι : L →ₐ[K] Ω) : FiniteDimensional K ι.fieldRange :=
  LinearEquiv.finiteDimensional ι.equivFieldRange.toLinearEquiv

def artinOfEmbedding (ι : L →ₐ[K] Ω) : Kˣ →* (L ≃ₐ[K] L) :=
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  (AlgEquiv.autCongr ι.equivFieldRange).symm.toMonoidHom.comp
    ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω))

theorem apply_artinOfEmbedding (ι : L →ₐ[K] Ω) (x : Kˣ) (z : L) :
    ι (artinOfEmbedding ι x z) =
      ((localArtinMap K Ω x ⟨ι z, (have := isAbelianGalois_fieldRange ι;
        le_maximalAbelianExtension ι.fieldRange) ⟨z, rfl⟩⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have h : ι (artinOfEmbedding ι x z) =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _) (localArtinMap K Ω x)
        (ι.equivFieldRange z) : ι.fieldRange) : Ω) := by
    simp only [artinOfEmbedding, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
    rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]
    rfl
  rw [h, restrictAb_apply]
  rfl

theorem artinOfEmbedding_eq (ι₁ ι₂ : L →ₐ[K] Ω) : artinOfEmbedding ι₁ = artinOfEmbedding ι₂ := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable ι₁.fieldRange Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K ι₁.fieldRange Ω
  obtain ⟨φ, hφ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι₁.fieldRange
    (M := Ω) (E := Ω) (ι₂.comp ι₁.equivFieldRange.symm.toAlgHom)
  have hφι : ∀ z : L, φ (ι₁ z) = ι₂ z := by
    intro z
    have := congrArg (fun f : ι₁.fieldRange →ₐ[K] Ω => f (ι₁.equivFieldRange z)) hφ
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  set τ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  set t := topologicalAbelianizationEquiv K Ω (τ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))
  have ht : ∀ w : maximalAbelianExtension K Ω, ((t w : maximalAbelianExtension K Ω) : Ω) = τ w :=
    fun w => topologicalAbelianizationEquiv_mk_apply K Ω τ w
  ext x z
  have key : ι₂ (artinOfEmbedding ι₁ x z) = ι₂ (artinOfEmbedding ι₂ x z) := by
    rw [← hφι (artinOfEmbedding ι₁ x z), apply_artinOfEmbedding ι₂]
    change τ (ι₁ (artinOfEmbedding ι₁ x z)) = _
    rw [apply_artinOfEmbedding ι₁]
    set w : maximalAbelianExtension K Ω := ⟨ι₁ z, (have := isAbelianGalois_fieldRange ι₁;
      le_maximalAbelianExtension ι₁.fieldRange) ⟨z, rfl⟩⟩
    have htw : t w = ⟨ι₂ z, (have := isAbelianGalois_fieldRange ι₂;
        le_maximalAbelianExtension ι₂.fieldRange) ⟨z, rfl⟩⟩ :=
      Subtype.ext ((ht w).trans (hφι z))
    have hc : (localArtinMap K Ω x) (t w) = t ((localArtinMap K Ω x) w) := by
      rw [← AlgEquiv.mul_apply, mul_comm' (localArtinMap K Ω x) t, AlgEquiv.mul_apply]
    rw [← ht, ← hc, htw]
  exact ι₂.injective key

variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [IsSepClosure K Ω']

theorem artinOfEmbedding_algEquiv_comp (ε : Ω ≃ₐ[K] Ω') (ι : L →ₐ[K] Ω) :
    artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) = artinOfEmbedding ι := by
  ext x z
  have key : ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) x z) =
      ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ι x z) := by
    rw [apply_artinOfEmbedding]
    change _ = ε (ι (artinOfEmbedding ι x z))
    rw [apply_artinOfEmbedding, localArtinMap_algEquiv_apply]
    rfl
  exact ((ε : Ω →ₐ[K] Ω').comp ι).injective key

end Embedding

section Intrinsic


variable (K L) in
def localArtinMapOfField : Kˣ →* (L ≃ₐ[K] L) :=
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  artinOfEmbedding (IsSepClosed.lift : L →ₐ[K] SeparableClosure K)

theorem localArtinMapOfField_eq_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (ι : L →ₐ[K] Ω) : localArtinMapOfField K L = artinOfEmbedding ι := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  let ε : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  rw [localArtinMapOfField, ← artinOfEmbedding_algEquiv_comp ε]
  exact artinOfEmbedding_eq _ _

theorem surjective_localArtinMapOfField : Function.Surjective (localArtinMapOfField K L) := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  set ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  intro σ
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := SeparableClosure K) ι.fieldRange
    (AlgEquiv.autCongr ι.equivFieldRange σ)
  refine ⟨x, ?_⟩
  change (AlgEquiv.autCongr ι.equivFieldRange).symm _ = σ
  rw [hx, MulEquiv.symm_apply_apply]

end Intrinsic

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalArtinFunctoriality
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem vle_algEquiv_apply_iff {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L'] [ValuativeRel L] [ValuativeRel L']
    [ValuativeExtension K L] [ValuativeExtension K L'] (e : L ≃ₐ[K] L') (x y : L) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  rw [vle_iff_spectralNorm_le (K := K), vle_iff_spectralNorm_le (K := K)]
  simp only [spectralNorm, minpoly.algEquiv_eq]

end Valuation

section Conjugation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] (σ : Ω ≃ₐ[K] Ω)

end Conjugation

section Finite

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [IsSepClosure K Ω] [IsSepClosure K' Ω]


omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeExtension K K'] in
theorem maximalAbelianExtension_le_of_algebra {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    y ∈ maximalAbelianExtension K' Ω := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  exact (mem_maximalAbelianExtension_transport_iff (AlgHom.equivFieldRange ι).toRingEquiv
    (RingEquiv.refl Ω) (fun _ => rfl)).1 (maximalAbelianExtension_le_restrictScalars ι.fieldRange hy)

theorem localArtinMap_apply_of_algebra (x : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
      maximalAbelianExtension K' Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  set e := AlgHom.equivFieldRange ι
  have he : ∀ a b : K', e a ≤ᵥ e b ↔ a ≤ᵥ b := vle_algEquiv_apply_iff e
  have h1 := transport_localArtinMap_apply e.toRingEquiv he (RingEquiv.refl Ω) (fun _ => rfl) x
    (maximalAbelianExtension_le_of_algebra hy)
  simp only [RingEquiv.refl_apply] at h1
  rw [h1, localArtinMap_apply_of_mem ι.fieldRange _ hy]
  congr 3
  ext
  rw [coe_normUnits, coe_normUnits]
  exact Algebra.norm_eq_of_algEquiv e x

end Finite

end GroundTheory.LocalField
end
end

