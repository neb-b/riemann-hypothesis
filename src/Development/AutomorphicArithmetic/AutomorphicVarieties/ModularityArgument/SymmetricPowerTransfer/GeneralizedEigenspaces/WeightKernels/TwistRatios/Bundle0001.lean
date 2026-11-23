module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0059

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.AutIso
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

private theorem act_conj (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) k) *ᵥ ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hg]
  congr 2
  group

private theorem ss_iso (h : RepIso r r') (hr : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) hr
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

private theorem irr_iso (h : RepIso r r') (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨hr.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun _ => rfl
  have hinv := hr.2.2 (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) le_top (fun s v hv => by
    change e _ ∈ W
    have h1 : e v ∈ W := hv
    rw [he] at h1 ⊢
    rw [← act_conj g hg]
    exact hW s _ h1)
  have hW' : W = (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective e.surjective W).symm
  rcases hinv with h0 | h0
  · left
    rw [hW', h0, Submodule.map_bot]
  · right
    rw [hW', h0, Submodule.map_top, LinearEquiv.range]

private theorem tw_iso (χ : Γ →* kˣ) (h : RepIso r r') : RepIso (tw r χ) (tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  simp only [Units.val_mul, tw_val, hg s, Matrix.mul_smul, Matrix.smul_mul]

private theorem comp_iso {Γ' : Type} [Group Γ'] (φ : Γ' →* Γ) (h : RepIso r r') : RepIso (r.comp φ) (r'.comp φ) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun s => hg (φ s)⟩

end Rep

private theorem att_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    (h : RepIso r r') (H : AttachedSys ι r sat) : AttachedSys ι r' sat :=
  ⟨ss_iso h H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

end UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso

open UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso in
theorem UpperTheory.V.Z.Sym.Ga.autIso :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G L Ω →* GL (Fin n) (Qbar l)), RepIso r r' → (IsAutC ι r → IsAutC ι r') ∧ (IsAutCsd ι r → IsAutCsd ι r') ∧ (IsIrr r → IsIrr r') ∧ (IrrOpen r → IrrOpen r') ∧ RepIso r' r ∧ ∀ ξ, RepIso (tw r ξ) (tw r' ξ) := by
  intro L Ω _ _ _ _ _ _ l _ ι n r r' h
  refine ⟨?_, ?_, irr_iso h, ?_, h.symm', fun ξ => tw_iso ξ h⟩
  · rintro ⟨π, h1, h2⟩
    exact ⟨π, h1, att_iso h h2⟩
  · rintro ⟨π, h1, h2, h3⟩
    exact ⟨π, h1, h2, att_iso h h3⟩
  · intro hr H hH
    exact irr_iso (comp_iso H.subtype h) (hr H hH)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.BadClosed
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.badClosed :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → (Continuous fun g => Ga.uf (r g)) ∧ (Continuous fun g : G L Ω => Ga.ep l g) ∧ IsClosed (Ga.Bad r) := by
  intro L Ω _ _ _ _ _ l _ r hr
  have hm : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hU : Continuous fun g => Ga.uf (r g) := by
    unfold Ga.uf Ga.tr
    refine ((hm.matrix_trace.pow 2).div hm.matrix_det fun g => ?_).sub continuous_const
    exact (Matrix.isUnits_det_units (r g)).ne_zero
  have hE : Continuous fun g : G L Ω => Ga.ep l g := by
    have hu : Continuous fun g : G L Ω => ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) :=
      (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ L Ω l)
    have hz : Continuous fun g : G L Ω => (((cycZ L Ω l g : ℤ_[l]) : ℚ_[l])) :=
      continuous_subtype_val.comp hu
    have h := (continuous_algebraMap ℚ_[l] (Qbar l)).comp hz
    convert h using 1
    funext g
    rfl
  have hne : ∀ g : G L Ω, Ga.ep l g ≠ 0 := fun g => (cycBar L Ω l g).ne_zero
  refine ⟨hU, hE, ?_⟩
  have hset : Ga.Bad r = ⋃ m ∈ Finset.Icc (-2 : ℤ) 2,
      {g | Ga.uf (r g) ^ 2 - 2 = Ga.ep l g ^ m + Ga.ep l g ^ (-m)} := by
    ext g
    simp only [Ga.Bad, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop, abs_le]
  rw [hset]
  refine isClosed_biUnion_finset fun m _ => isClosed_eq ((hU.pow 2).sub continuous_const) ?_
  exact (hE.zpow₀ m fun g => Or.inl (hne g)).add (hE.zpow₀ (-m) fun g => Or.inl (hne g))
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjEx
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma conj_real {K : Type} [Field K] [NumberField K] [IsTotallyReal K] (φ : K →+* ℂ) (x : K) :
    starRingEnd ℂ (φ x) = φ x := by
  have h : ComplexEmbedding.IsReal φ :=
    InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (InfinitePlace.mk φ))
  exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp h) x

private lemma exists_emb (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [Algebra.IsAlgebraic L Ω] : Nonempty (Ω →+* ℂ) := by
  let φ : L →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom
  letI : Algebra L ℂ := φ.toAlgebra
  exact ⟨(IsAlgClosed.lift (R := L) (S := Ω) (M := ℂ)).toRingHom⟩

theorem UpperTheory.V.Z.Sym.Ga.conjEx :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], ∃ c : G (maximalRealSubfield L) Ω, IsConjEl c := by
  intro L Ω _ _ _ _ _ _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ L Ω
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  obtain ⟨j⟩ := exists_emb L Ω
  let j' : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let τ' : Ω →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp j).toRatAlgHom
  let e : Ω ≃ₐ[ℚ] j'.fieldRange :=
    (AlgEquiv.ofInjectiveField j').trans (Subalgebra.equivOfEq _ _ (AlgHom.fieldRange_toSubalgebra j').symm)
  have hN : Normal ℚ j'.fieldRange := Normal.of_algEquiv e
  have hr := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ j'.fieldRange hN (τ'.comp e.symm.toAlgHom)
  have hex : ∀ x : Ω, ∃ y : Ω, j y = starRingEnd ℂ (j x) := by
    intro x
    have hmem : τ' x ∈ (τ'.comp e.symm.toAlgHom).fieldRange :=
      AlgHom.mem_fieldRange.mpr ⟨e x, by simp⟩
    have hmem' : τ' x ∈ j'.fieldRange := hr ▸ hmem
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hmem'
    exact ⟨y, hy⟩
  choose σ hσ using hex
  have inj := j.injective
  let c : Ω ≃ₐ[maximalRealSubfield L] Ω :=
    { toFun := σ
      invFun := σ
      left_inv := fun x => inj (by rw [hσ, hσ, Complex.conj_conj])
      right_inv := fun x => inj (by rw [hσ, hσ, Complex.conj_conj])
      map_mul' := fun x y => inj (by simp only [hσ, map_mul])
      map_add' := fun x y => inj (by simp only [hσ, map_add (f := _)])
      commutes' := fun r => inj (by
        rw [hσ]
        exact conj_real (j.comp (algebraMap (maximalRealSubfield L) Ω)) r) }
  exact ⟨c, j, fun x => hσ x⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjFrob
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise in
private theorem cf_stab {H Ω : Type} [Field Ω] [Group H] [MulSemiringAction H Ω] (g : H) (B : ValuationSubring Ω)
    (h : ∀ y : Ω, g • y ∈ B ↔ y ∈ B) : g • B = B := by
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have key := h (g⁻¹ • y)
  simp only [smul_inv_smul] at key
  exact key.symm

private theorem cf_on {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {c : G (maximalRealSubfield L) Ω} (hc : IsConjEl c) (x : L) :
    c (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x).symm

private theorem cf_on_inv {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {c : G (maximalRealSubfield L) Ω} (hc : IsConjEl c) (x : L) :
    c.symm (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  have h := IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x
  simp only [RingHom.comp_apply] at h
  have h2 := hj (c.symm (algebraMap L Ω x))
  simp only [AlgEquiv.apply_symm_apply] at h2
  rw [h, h2, Complex.conj_conj]

private theorem cf_primes {L : Type} [Field L] [NumberField L] [IsCMField L] (w w' : Plc L)
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ ∀ x : 𝓞 L, x ∈ w'.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  unfold Plc at w w'
  unfold Lp at h
  have h' : w.asIdeal.under (𝓞 (maximalRealSubfield L)) = w'.asIdeal.under (𝓞 (maximalRealSubfield L)) := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 (maximalRealSubfield L)) (𝓞 L)
    (L ≃ₐ[maximalRealSubfield L] L) w.asIdeal w'.asIdeal h'
  have hmem : g ∈ Subgroup.zpowers (IsCMField.complexConj L) := by
    rw [IsCMField.zpowers_complexConj_eq_top]
    trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, IsCMField.orderOf_complexConj] at hg
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [Nat.cast_ofNat, hk, zpow_zero, one_smul] at hg
    exact HeightOneSpectrum.ext hg
  · right
    intro x
    rw [Nat.cast_ofNat, hk, zpow_one] at hg
    rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (IsCMField.complexConj L)⁻¹ = IsCMField.complexConj L := by
      apply inv_eq_of_mul_eq_one_right
      ext y
      simp
    have hx : (IsCMField.complexConj L)⁻¹ • x = IsCMField.ringOfIntegersComplexConj L x := by
      rw [hinv]
      ext
      simp
      rfl
    rw [hx]

open scoped Pointwise in
theorem UpperTheory.V.Z.Sym.Ga.conjFrob :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (c : G (maximalRealSubfield L) Ω), IsConjEl c → ∀ w w' : Plc L, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → ∀ s, Ga.FrobAt w s → Ga.FrobAt w' s ∨ ∃ s', Ga.FrobAt w' s' ∧ s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ := by
  intro L Ω _ _ _ _ _ _ c hc w w' hw s hs
  rcases cf_primes w w' hw with rfl | hx
  · exact Or.inl hs
  right
  unfold Ga.FrobAt at hs
  obtain ⟨A, hA, hF⟩ := hs
  unfold IsFrob at hF
  obtain ⟨hdec, hfr⟩ := hF
  let e : 𝓞 L ≃+* 𝓞 L := (IsCMField.ringOfIntegersComplexConj L).toRingEquiv
  have hq : normV w' = normV w := by
    unfold normV
    refine Nat.card_congr (Ideal.quotientEquiv w'.asIdeal w.asIdeal e ?_).toEquiv
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap, hx]
    simp [e]
  have hsA : ∀ z : Ω, s z ∈ A ↔ z ∈ A := by
    intro z
    have hstab : s • A = A := MulAction.mem_stabilizer_iff.mp hdec
    nth_rewrite 1 [← hstab]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  let A' : ValuationSubring Ω := A.comap (c.symm : Ω ≃+* Ω).toRingHom
  have hmem : ∀ y : Ω, (c : Ω ≃+* Ω) y ∈ A' ↔ y ∈ A := by
    intro y
    simp [A', ValuationSubring.mem_comap]
  let t : Ω ≃ₐ[maximalRealSubfield L] Ω := c * s.restrictScalars (maximalRealSubfield L) * c⁻¹
  have hfix : ∀ x : L, t.toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := by
    intro x
    change c (s (c⁻¹ (algebraMap L Ω x))) = algebraMap L Ω x
    rw [AlgEquiv.aut_inv, cf_on_inv hc, AlgEquiv.commutes, cf_on hc, IsCMField.complexConj_apply_apply]
  let s' : G L Ω := AlgEquiv.ofRingEquiv (f := t.toRingEquiv) hfix
  have hs' : ∀ y, s' y = c (s (c.symm y)) := by
    intro y
    rfl
  refine ⟨s', ?_, ?_⟩
  · unfold Ga.FrobAt
    refine ⟨A', ?_, ?_⟩
    · unfold IsPlaceOver
      intro x
      rw [hx x, ← hA]
      have hcx : algebraMap L Ω x = (c : Ω ≃+* Ω) (algebraMap L Ω (IsCMField.ringOfIntegersComplexConj L x)) := by
        change algebraMap L Ω x = c (algebraMap L Ω (IsCMField.complexConj L x))
        rw [cf_on hc, IsCMField.complexConj_apply_apply]
      rw [hcx]
      exact val_lt_one hmem _
    · rw [hq]
      unfold IsFrob
      constructor
      · apply MulAction.mem_stabilizer_iff.mpr
        apply cf_stab
        intro y
        rw [AlgEquiv.smul_def, hs']
        change c.symm (c (s (c.symm y))) ∈ A ↔ c.symm y ∈ A
        rw [AlgEquiv.symm_apply_apply, hsA]
      · intro y hy
        rw [ValuationSubring.valuation_le_one_iff] at hy
        have hz : c.symm y ∈ A := hy
        have hd : s' y - y ^ normV w = (c : Ω ≃+* Ω) (s (c.symm y) - (c.symm y) ^ normV w) := by
          rw [hs', map_sub, map_pow]
          change c (s (c.symm y)) - y ^ normV w = c (s (c.symm y)) - (c (c.symm y)) ^ normV w
          rw [AlgEquiv.apply_symm_apply]
        rw [hd, val_lt_one hmem]
        exact hfr _ ((ValuationSubring.valuation_le_one_iff _ _).mpr hz)
  · ext y
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Coset
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.coset :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (V : Set Γ), IsOpen V → ∀ g ∈ V, ∃ H : Subgroup Γ, H.Normal ∧ IsOpen (H : Set Γ) ∧ ∀ h ∈ H, g * h ∈ V := by
  intro Γ _ _ _ _ _ V hV g hg
  have hU : IsOpen ((fun x : Γ => g * x) ⁻¹' V) := hV.preimage (continuous_const_mul g)
  have h1 : (1 : Γ) ∈ (fun x : Γ => g * x) ⁻¹' V := by simpa using hg
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  exact ⟨H.toSubgroup, H.isNormal', H.isOpen', fun h hh => hH hh⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.EpsAway
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga

private theorem cyc_eq_of_pow {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal)
    (h : IsPlaceOver A w) {σ : G L Ω} {q : ℕ}
    (hσ : ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) :
    (cycBar L Ω l σ : Qbar l) = (q : Qbar l) := by
  have h1 : ((cycZ L Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hσ)
  simp [cycBar, h1]

end UpperTheory.V.Z.Sym.Ga

theorem UpperTheory.V.Z.Sym.Ga.epsAway :
    Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ s : Weil h, ι (Ga.ep l (s : G L Ω)) = (absPow (w.adicCompletion L) 1 (a s) : ℂ) ∧ ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
  intro _ L Ω _ _ _ _ _ l _ ι w hl A h a ha s
  have hfrob : (cycBar L Ω l ((frob h : Weil h) : G L Ω) : Qbar l) = ((normV w : ℕ) : Qbar l) :=
    Ga.cyc_eq_of_pow hl h (isFrob_frob (h := h)).2
  set t : Weil h := s * (frob h) ^ (-deg s) with ht
  have hdt : deg t = 0 := by
    rw [ht, deg_mul, deg_zpow, deg_frob]
    ring
  have hI : (t : G L Ω) ∈ Ine (F := L) A :=
    actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hdt))
  have hine : (cycBar L Ω l (t : G L Ω) : Qbar l) = 1 := by
    have := Ga.cyc_eq_of_pow (σ := (t : G L Ω)) (q := 1) hl h (fun x hx => by simpa using hI.2 x hx)
    simpa using this
  have hs : s = t * (frob h) ^ (deg s) := by
    rw [ht, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hε : Ga.ep l (s : G L Ω) = ((normV w : ℕ) : Qbar l) ^ deg s := by
    show (cycBar L Ω l (s : G L Ω) : Qbar l) = _
    conv_lhs => rw [hs]
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, hine, one_mul, Subgroup.coe_zpow, map_zpow,
      Units.val_zpow_eq_zpow_val, hfrob]
  have hq : ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
    rw [hε, map_zpow₀, map_natCast]
  refine ⟨?_, hq⟩
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [hq, ← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val]
  simp
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.KerLe
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.kerLe :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (H : Type) [Group H] (n : ℕ) (R : H →* GL (Fin n) k), IsIrr R → ∀ (x₀ : GL (Fin n) k) (B : Type) [Ring B] [Algebra k B] [Module.Finite k B] (φ : H →* B) (f : B →ₗ[k] k), (∀ h, Ga.tr (x₀ * R h) = f (φ h)) → n ^ 2 ≤ Module.finrank k (Algebra.adjoin k (Set.range φ)) ∧ ∀ x : MonoidAlgebra k H, MonoidAlgebra.lift k B H φ x = 0 → MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H ((Units.coeHom _).comp R) x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe26.kerLe
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Select
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.select :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (X : Set (Plc L)), ∃ P ⊆ X, Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) P ∧ ∀ w ∈ X, ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := by
  intro L _ _ _ X
  rcases isEmpty_or_nonempty (Plc L) with hE | hN
  · refine ⟨∅, Set.empty_subset _, Set.injOn_empty _, ?_⟩
    intro w
    exact (IsEmpty.false w).elim
  set f : Plc L → _ := fun w : Plc L => w.under (𝓞 (Lp L)) with hf
  have spec : ∀ w ∈ X, Classical.epsilon (fun v => v ∈ X ∧ f v = f w) ∈ X ∧
      f (Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) = f w :=
    fun w hw => Classical.epsilon_spec (p := fun v => v ∈ X ∧ f v = f w) ⟨w, hw, rfl⟩
  refine ⟨(fun w => Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) '' X, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (spec w hw).1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hab' : f a = f b := by
      have := hab
      simp only at this
      rw [(spec a ha).2, (spec b hb).2] at this
      exact this
    simp only [hab']
  · intro w hw
    exact ⟨_, ⟨w, hw, rfl⟩, (spec w hw).2⟩
end
end

