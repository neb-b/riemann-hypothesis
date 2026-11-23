module

public import Mathlib
public import GroundTheory.LocalFields.ConductorLubinTate
public import GroundTheory.LocalFields.Bundle0015
public import GroundTheory.LocalFields.LocalArtinMap
public import GroundTheory.LocalFields.KroneckerWeber

@[expose] public section

-- bundled from GroundTheory.LocalFields.ConductorReciprocity
section
noncomputable section

open ValuativeRel GroundTheory.LocalField.FormalGroup GroundTheory.LocalField.Abstract

namespace GroundTheory.LocalField

section Bridge

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units


include hf in
theorem restrictAb_localArtinMap_lubinTate {n : ℕ} (hn : 0 < n) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E] (hE : E ≤ maximalUnramifiedExtension K Ω)
    [IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)]
    (u : 𝒪[K]ˣ) (k : ℤ) (τ : Ω ≃ₐ[K] Ω)
    (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    restrictAb (lubinTateField Ω hπ hf n ⊔ E) (le_maximalAbelianExtension _)
        (localArtinMap K Ω (unitUniformizerPow hπ u k)) =
      AlgEquiv.restrictNormalHom (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) τ := by
  rw [restrictAb_localArtinMap]
  apply (bijective_abelianizationOf _).1
  rw [of_localReciprocityAbelian_symm]
  have hrec := reciprocity_lubinTate_sup hπ hf hn E hE u k τ hτd hτ
  have h2 := localReciprocity_symm_mk_baseUnitsEquiv (lubinTateField Ω hπ hf n ⊔ E)
    (baseUnitsEquiv.symm (unitUniformizerPow hπ u k))
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2]
  have h3 : ((localClassFieldData K Ω).reciprocityAbEquiv
      (le_top : fixingOpenSubgroup (lubinTateField Ω hπ hf n ⊔ E) ≤ ⊤)
      (classFieldAxiom_units K Ω)).symm
        ((baseUnitsEquiv.symm (unitUniformizerPow hπ u k) : fixedModule Ωˣ
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) : tateZero Ωˣ _ _) =
      Group.Abelianization.of (QuotientGroup.mk
        (⟨τ, by simp⟩ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)))) := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of]
    exact hrec.symm
  rw [h3, abelianizationCongr_of, baseQuotientEquiv_mk]
  rfl

section Compositum

variable {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω} [FiniteDimensional K E] [IsGalois K E]
  (hE : IsUnramifiedSubextension E)


include hn hE in
theorem mem_upperRamificationGroup_lubinTateField_sup {v : ℝ} (hv : -1 < v)
    (σ : (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) ≃ₐ[K]
      (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)) :
    σ ∈ upperRamificationGroup K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) v ↔
      restrictAut le_sup_right σ = 1 ∧
        restrictAut le_sup_left σ ∈ lubinTateUnitSubgroup hπ hf n ⌈v⌉.toNat := by
  have hT := map_upperRamificationGroup_restrictAut
    (le_sup_left : lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hf n ⊔ E) v
  rw [upperRamificationGroup_lubinTateField] at hT
  have hEv := map_upperRamificationGroup_restrictAut
    (le_sup_right : E ≤ lubinTateField Ω hπ hf n ⊔ E) v
  rw [upperRamificationGroup_eq_bot_of_ramificationIndex_eq_one hE.ramificationIndex_eq_one hv] at hEv
  constructor
  · intro hσ
    refine ⟨?_, ?_⟩
    · have := Subgroup.mem_map_of_mem (restrictAut (le_sup_right :
        E ≤ lubinTateField Ω hπ hf n ⊔ E)) hσ
      rwa [hEv, Subgroup.mem_bot] at this
    · rw [← hT]
      exact Subgroup.mem_map_of_mem _ hσ
  · rintro ⟨h1, h2⟩
    rw [← hT] at h2
    obtain ⟨σ', hσ', he⟩ := h2
    have h1' : restrictAut (le_sup_right : E ≤ lubinTateField Ω hπ hf n ⊔ E) σ' = 1 := by
      have := Subgroup.mem_map_of_mem (restrictAut (le_sup_right :
        E ≤ lubinTateField Ω hπ hf n ⊔ E)) hσ'
      rwa [hEv, Subgroup.mem_bot] at this
    have : σ' = σ := (bijective_restrictAut_prod hπ hf hn hE).1 (Prod.ext he (h1'.trans h1.symm))
    exact this ▸ hσ'


include hn hE in
theorem restrictAut_localArtinMap_unitsIncl
    [IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)] (u : 𝒪[K]ˣ) :
    restrictAut le_sup_right (restrictAb (lubinTateField Ω hπ hf n ⊔ E) (le_maximalAbelianExtension _)
        (localArtinMap K Ω (unitsIncl K u))) = 1 ∧
      lubinTateChar hπ hf n le_sup_left (restrictAb (lubinTateField Ω hπ hf n ⊔ E)
        (le_maximalAbelianExtension _) (localArtinMap K Ω (unitsIncl K u))) = unitsMk π n u⁻¹ := by
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u 0
  have hx : unitsIncl K u = unitUniformizerPow hπ u 0 := by
    rw [unitUniformizerPow_eq, zpow_zero, one_mul]
  rw [hx, restrictAb_localArtinMap_lubinTate hπ hf hn E hE.le_maximalUnramifiedExtension u 0 τ hτd hτ]
  have hτ1 : τ ∈ (maximalUnramifiedExtension K Ω).fixingSubgroup := by
    rw [← ker_unramifiedDegree, MonoidHom.mem_ker, hτd]
    simp
  refine ⟨?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [restrictAut_apply, AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ1 x
      (hE.le_maximalUnramifiedExtension x.2)
  · apply Units.ext
    rw [lubinTateChar_eq_of_apply hπ hf le_sup_left _ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]), coe_unitsMk]
    intro x hx
    rw [AlgEquiv.restrictNormalHom_apply, ← hτ x hx, lubinTateGalPointMap_val]


include hn hE in
theorem map_unitFiltrationUnits_lubinTateField_sup
    [IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)] (j : ℕ) :
    (unitFiltrationUnits K j).map ((restrictAb (lubinTateField Ω hπ hf n ⊔ E)
        (le_maximalAbelianExtension _)).comp (localArtinMap K Ω)) =
      upperRamificationGroup K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) j := by
  ext σ
  have hj : (-1 : ℝ) < j := by have := j.cast_nonneg (α := ℝ); linarith
  rw [mem_upperRamificationGroup_lubinTateField_sup hπ hf hn hE hj, Int.ceil_natCast,
    Int.toNat_natCast, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨h1, h2⟩ := restrictAut_localArtinMap_unitsIncl hπ hf hn hE u
    refine ⟨h1, ?_⟩
    rw [lubinTateUnitSubgroup, Subgroup.mem_comap]
    exact ⟨u⁻¹, inv_mem hu, h2.symm⟩
  · rintro ⟨h1, w, hw, hwσ⟩
    refine ⟨unitsIncl K w⁻¹, ⟨w⁻¹, inv_mem hw, rfl⟩, ?_⟩
    obtain ⟨g1, g2⟩ := restrictAut_localArtinMap_unitsIncl hπ hf hn hE w⁻¹
    apply (bijective_restrictAut_prod hπ hf hn hE).1
    refine Prod.ext ?_ (g1.trans h1.symm)
    apply (lubinTateGalEquiv hπ hf n).injective
    change lubinTateChar hπ hf n le_sup_left _ = _
    rw [MonoidHom.comp_apply, g2, inv_inv]
    exact hwσ

end Compositum

end Bridge

section Abelian

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in
theorem restrictAb_eq_restrictAut_comp {L M : IntermediateField K Ω} [Normal K L] [Normal K M]
    (h : L ≤ M) (hM : M ≤ maximalAbelianExtension K Ω) :
    restrictAb L (h.trans hM) = (restrictAut h).comp (restrictAb M hM) := by
  refine MonoidHom.ext fun σ => AlgEquiv.ext fun x => Subtype.ext ?_
  rw [MonoidHom.comp_apply, restrictAut_apply, restrictAb_apply, restrictAb_apply]

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem exists_le_lubinTateField_sup :
    ∃ (π : 𝒪[K]) (hπ : Irreducible π) (n : ℕ) (E : IntermediateField K Ω),
      0 < n ∧ IsUnramifiedSubextension E ∧
        L ≤ lubinTateField Ω hπ (isLubinTateSeries_ltPoly π) n ⊔ E := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨n, m, hLM⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ (isLubinTateSeries_ltPoly π) L
  exact ⟨π, hπ, n + 1, unramifiedTower K Ω m, n.succ_pos, isUnramifiedSubextension_unramifiedTower m,
    hLM⟩

theorem map_unitFiltrationUnits_restrictAb_localArtinMap (n : ℕ) :
    (unitFiltrationUnits K n).map
        ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) =
      upperRamificationGroup K L n := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨π, hπ, k, E, hk, hE, hLM⟩ := exists_le_lubinTateField_sup L (Ω := Ω)
  have := hE.1
  have := hE.isGalois
  have := isAbelianGalois_lubinTateField_sup hπ (isLubinTateSeries_ltPoly π) hk hE
  rw [restrictAb_eq_restrictAut_comp hLM (le_maximalAbelianExtension _), MonoidHom.comp_assoc,
    ← Subgroup.map_map, map_unitFiltrationUnits_lubinTateField_sup hπ (isLubinTateSeries_ltPoly π) hk hE,
    map_upperRamificationGroup_restrictAut hLM]

theorem upperRamificationGroup_eq_ceil (v : ℝ) :
    upperRamificationGroup K L v = upperRamificationGroup K L ⌈v⌉ := by
  rcases le_or_gt v (-1) with hv | hv
  · have hc : ((⌈v⌉ : ℤ) : ℝ) ≤ -1 := by
      have : ⌈v⌉ ≤ -1 := Int.ceil_le.2 (by push_cast; exact hv)
      exact_mod_cast this
    rw [upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hv,
      upperRamificationGroup_of_nonpos (by linarith), lowerRamificationGroupReal_eq_top hc]
  · have : IsSepClosed Ω := IsSepClosure.sep_closed K
    obtain ⟨π, hπ, k, E, hk, hE, hLM⟩ := exists_le_lubinTateField_sup L (Ω := Ω)
    have := hE.1
    have := hE.isGalois
    have hv' : -1 < ((⌈v⌉ : ℤ) : ℝ) := hv.trans_le (Int.le_ceil v)
    rw [← map_upperRamificationGroup_restrictAut hLM v,
      ← map_upperRamificationGroup_restrictAut hLM (⌈v⌉ : ℝ)]
    congr 1
    ext σ
    rw [mem_upperRamificationGroup_lubinTateField_sup hπ _ hk hE hv,
      mem_upperRamificationGroup_lubinTateField_sup hπ _ hk hE hv', Int.ceil_intCast]

end Abelian

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalArtinUniqueness
section
noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel GroundTheory.LocalField.FormalGroup

section Galois

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem apply_eq_self_of_mem_sup {τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    {E₁ E₂ : IntermediateField F Ω} (h₁ : E₁ ≤ maximalAbelianExtension F Ω)
    (h₂ : E₂ ≤ maximalAbelianExtension F Ω)
    (hτ₁ : ∀ (y : Ω) (hy : y ∈ E₁), ((τ ⟨y, h₁ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y)
    (hτ₂ : ∀ (y : Ω) (hy : y ∈ E₂), ((τ ⟨y, h₂ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y)
    (y : Ω) (hy : y ∈ E₁ ⊔ E₂) :
    ((τ ⟨y, sup_le h₁ h₂ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm τ)
  have hτ : τ = topologicalAbelianizationEquiv F Ω (g : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hg, ContinuousMulEquiv.apply_symm_apply]
  subst hτ
  have hg : g ∈ (E₁ ⊔ E₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_,
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_⟩
    · have := hτ₁ z hz
      rwa [topologicalAbelianizationEquiv_mk_apply] at this
    · have := hτ₂ z hz
      rwa [topologicalAbelianizationEquiv_mk_apply] at this
  rw [topologicalAbelianizationEquiv_mk_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy

end Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Uniqueness

theorem monoidHom_ext_uniformizer {M : Type*} [Group M] {f g : Kˣ →* M}
    (h : ∀ {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ), f (uniformizerUnit hϖ) = g (uniformizerUnit hϖ)) :
    f = g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hunit : ∀ u : 𝒪[K]ˣ, f (unitsIncl K u) = g (unitsIncl K u) := by
    intro u
    have huϖ : Irreducible ((u : 𝒪[K]) * ϖ) := (irreducible_units_mul u).2 hϖ
    have he : unitsIncl K u = uniformizerUnit huϖ * (uniformizerUnit hϖ)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      ext
      simp [coe_uniformizerUnit]
    rw [he, map_mul, map_mul, map_inv, map_inv, h huϖ, h hϖ]
  ext x
  set e := unitsEquivIntProd hϖ
  have hx : x = uniformizerUnit hϖ ^ Multiplicative.toAdd (e x).1 * unitsIncl K (e x).2 := by
    apply e.injective
    rw [map_mul, map_zpow, unitsEquivIntProd_uniformizer, unitsEquivIntProd_unitsIncl]
    ext
    · simp [← ofAdd_zsmul]
    · simp
  rw [hx, map_mul, map_mul, map_zpow, map_zpow, h hϖ, hunit]

theorem eq_localArtinMap_of
    {ψ : Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)}
    (hFrob : ∀ π : Kˣ, ord (π : K) = 1 →
      restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
        (ψ π) = maximalUnramifiedExtensionFrobenius K Ω)
    (hnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      ∀ x ∈ (normUnits K L).range, restrictAb L (le_maximalAbelianExtension L) (ψ x) = 1) :
    ψ = localArtinMap K Ω := by
  refine monoidHom_ext_uniformizer fun {ϖ} hϖ => ?_
  set π := uniformizerUnit hϖ
  have hπ : ord (π : K) = 1 := ord_uniformizer hϖ
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf : IsLubinTateSeries ϖ (ltPoly ϖ : PowerSeries 𝒪[K]) := by
    have hq := one_lt_card_residueField' K
    refine ⟨?_, ?_, ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
      simp [Polynomial.coeff_X_pow, show 0 ≠ Nat.card 𝓀[K] by omega]
    · rw [Polynomial.coeff_coe, ltPoly]
      simp [Polynomial.coeff_X_pow, hq.ne]
    · intro k
      rw [coeff_ltPoly_sub, Polynomial.coeff_C_mul_X]
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero ϖ
  haveI (n : ℕ) : IsGalois K (lubinTateField Ω hϖ hf n) :=
    IsGalois.of_card_aut_eq_finrank K _
      ((Nat.card_congr (lubinTateGalEquiv (Ω := Ω) hϖ hf n).toEquiv).trans
        (card_units_quotient_eq_finrank (Ω := Ω) (hπ := hϖ) hf n))

  have hLT : ∀ (χ : Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω))
      (hχ : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        ∀ x ∈ (normUnits K L).range, restrictAb L (le_maximalAbelianExtension L) (χ x) = 1)
      (n : ℕ) (y : Ω) (hy : y ∈ lubinTateField Ω hϖ hf (n + 1)),
      ∃ hy' : y ∈ maximalAbelianExtension K Ω, ((χ π ⟨y, hy'⟩ : maximalAbelianExtension K Ω) : Ω) = y := by
    intro χ hχ n y hy
    have : IsAbelianGalois K (lubinTateField Ω hϖ hf (n + 1)) :=
      isAbelianGalois_of_mul_comm _ (lubinTateField_mul_comm hϖ hf (n + 1))
    refine ⟨le_maximalAbelianExtension _ hy, ?_⟩
    obtain ⟨z, hz⟩ := exists_norm_eq_uniformizer (Ω := Ω) hϖ hf n.succ_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hz
      exact coe_ne_zero_of_irreducible hϖ hz.symm
    have hmem : π ∈ (normUnits K (lubinTateField Ω hϖ hf (n + 1))).range :=
      ⟨Units.mk0 z hz0, Units.ext (by simpa [π, coe_uniformizerUnit] using hz)⟩
    have := congrArg (fun ρ : lubinTateField Ω hϖ hf (n + 1) ≃ₐ[K] lubinTateField Ω hϖ hf (n + 1) =>
      ((ρ ⟨y, hy⟩ : lubinTateField Ω hϖ hf (n + 1)) : Ω)) (hχ _ π hmem)
    simpa only [restrictAb_apply, AlgEquiv.one_apply] using this
  have hφnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      ∀ x ∈ (normUnits K L).range,
        restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) = 1 := by
    intro L _ _ x hx
    rw [← MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_restrictAb_localArtinMap]
    exact hx
  have hur : ∀ (y : Ω) (hy : y ∈ maximalUnramifiedExtension K Ω),
      ((ψ π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
        maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
        maximalAbelianExtension K Ω) : Ω) := by
    intro y hy
    have h1 := congrArg (fun ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω =>
      ((ρ ⟨y, hy⟩ : maximalUnramifiedExtension K Ω) : Ω)) (hFrob π hπ)
    have h2 := congrArg (fun ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω =>
      ((ρ ⟨y, hy⟩ : maximalUnramifiedExtension K Ω) : Ω)) (restrictAb_localArtinMap_uniformizer (Ω := Ω) hπ)
    simp only [restrictAb_apply] at h1 h2
    rw [h1, h2]

  set τ := (ψ π)⁻¹ * localArtinMap K Ω π
  have hτ1 : τ = 1 := by
    refine ext_restrictAb fun L _ _ => ?_
    obtain ⟨n, m, hLM⟩ := exists_le_lubinTateField_sup_unramifiedTower hϖ hf L
    have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
    have hM := isAbelianGalois_lubinTateField_sup hϖ hf n.succ_pos hE
    have h₁ : lubinTateField Ω hϖ hf (n + 1) ≤ maximalAbelianExtension K Ω :=
      (le_sup_left : lubinTateField Ω hϖ hf (n + 1) ≤
        lubinTateField Ω hϖ hf (n + 1) ⊔ unramifiedTower K Ω m).trans (le_maximalAbelianExtension _)
    have h₂ : unramifiedTower K Ω m ≤ maximalAbelianExtension K Ω :=
      (le_sup_right : unramifiedTower K Ω m ≤ lubinTateField Ω hϖ hf (n + 1) ⊔ _).trans
        (le_maximalAbelianExtension _)
    have hfix := apply_eq_self_of_mem_sup (τ := τ) h₁ h₂ (fun y hy => ?_) (fun y hy => ?_)
    · ext y
      rw [restrictAb_apply, map_one, AlgEquiv.one_apply]
      exact hfix y (hLM y.2)
    · obtain ⟨hy₁, hψ⟩ := hLT ψ hnorm n y hy
      obtain ⟨hy₂, hφ⟩ := hLT (localArtinMap K Ω) hφnorm n y hy
      simp only [τ, AlgEquiv.mul_apply]
      have : (localArtinMap K Ω π ⟨y, h₁ hy⟩) = ⟨y, h₁ hy⟩ := Subtype.ext hφ
      have h1 : (ψ π).symm ⟨y, h₁ hy⟩ = ⟨y, h₁ hy⟩ :=
        (AlgEquiv.symm_apply_eq _).2 (Subtype.ext hψ).symm
      rw [this, AlgEquiv.aut_inv, h1]
    · have hyur : y ∈ maximalUnramifiedExtension K Ω := unramifiedTower_le_maximalUnramifiedExtension m hy
      have h := hur y hyur
      simp only [τ, AlgEquiv.mul_apply]
      have h1 : (ψ π).symm (localArtinMap K Ω π ⟨y, h₂ hy⟩) = ⟨y, h₂ hy⟩ :=
        (AlgEquiv.symm_apply_eq _).2 (Subtype.ext h).symm
      rw [AlgEquiv.aut_inv, h1]
  rw [← inv_mul_eq_one]
  exact hτ1

end Uniqueness

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.NormCorrespondence
section
noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Index

theorem index_range_normUnits_of_isAbelianGalois (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] : (normUnits K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, ← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (localReciprocityAbelian L).toEquiv).symm

end Index

section Lattice


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem mul_comm_of_isAbelianGalois' (L : IntermediateField K Ω) [IsAbelianGalois K L]
    (σ τ : L ≃ₐ[K] L) : σ * τ = τ * σ :=
  mul_comm' σ τ

theorem range_normUnits_le_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsAbelianGalois K L] [IsAbelianGalois K L'] :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L :=
  range_normUnits_le_range_normUnits_iff (mul_comm_of_isAbelianGalois' L)
    (mul_comm_of_isAbelianGalois' L')

theorem exists_isAbelianGalois_range_normUnits_eq (H : Subgroup Kˣ) [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      (normUnits K L).range = H := by
  obtain ⟨L, hL, hG, hc, hLH⟩ := exists_range_normUnits_eq (Ω := Ω) H hH
  exact ⟨L, hL, { toIsGalois := hG, toIsMulCommutative := ⟨⟨hc⟩⟩ }, hLH⟩

end Lattice

section OrderIso


variable (K) in
def openFiniteIndexSubgroups : Set (Subgroup Kˣ) :=
  {H | IsOpen (H : Set Kˣ) ∧ H.FiniteIndex}


variable (K Ω) in
def normGroupMap (L : finiteAbelianExtensions K Ω) : openFiniteIndexSubgroups K :=
  have := L.2.1
  ⟨(normUnits K (L : IntermediateField K Ω)).range,
    isOpen_range_normUnits_and_finiteIndex (Ω := Ω) _⟩

theorem normGroupMap_injective : Function.Injective (normGroupMap K Ω) := by
  intro L L' h
  have := L.2.1
  have := L.2.2
  have := L'.2.1
  have := L'.2.2
  have h' : (normUnits K (L : IntermediateField K Ω)).range =
      (normUnits K (L' : IntermediateField K Ω)).range := congrArg Subtype.val h
  exact Subtype.ext (le_antisymm (range_normUnits_le_iff.1 h'.ge) (range_normUnits_le_iff.1 h'.le))

theorem normGroupMap_surjective : Function.Surjective (normGroupMap K Ω) := by
  intro H
  have := H.2.2
  obtain ⟨L, h1, h2, hL⟩ := exists_isAbelianGalois_range_normUnits_eq (Ω := Ω) H.1 H.2.1
  exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩

theorem normGroupMap_le_iff {L L' : finiteAbelianExtensions K Ω} :
    normGroupMap K Ω L ≤ normGroupMap K Ω L' ↔ L' ≤ L := by
  have := L.2.1
  have := L.2.2
  have := L'.2.1
  have := L'.2.2
  exact range_normUnits_le_iff


variable (K Ω) in
def normGroupOrderIso : finiteAbelianExtensions K Ω ≃o (openFiniteIndexSubgroups K)ᵒᵈ where
  toEquiv := (Equiv.ofBijective _ ⟨normGroupMap_injective, normGroupMap_surjective⟩).trans
    OrderDual.toDual
  map_rel_iff' := normGroupMap_le_iff

theorem normGroupOrderIso_apply (L : finiteAbelianExtensions K Ω) :
    (OrderDual.ofDual (normGroupOrderIso K Ω L)).1 =
      (have := L.2.1; (normUnits K (L : IntermediateField K Ω)).range) :=
  rfl

end OrderIso

end GroundTheory.LocalField
end
end

