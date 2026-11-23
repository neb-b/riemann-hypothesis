module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ExistsCompletionEquivOfHe
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormRam
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.V.Af.Bc
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam :
    NormRam := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ hp η hη A v hA hτ hunr
  obtain ⟨τ, hτI, hτM⟩ := hτ
  obtain ⟨hη1, hηp, hηev⟩ := hη
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have halg : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd hp.pos hηp
  obtain ⟨r, hrc, hr⟩ := hart.exists_isLAdicOf (ι : Qbar 2 ≃+* ℂ) halg
  have hrI : ∀ s ∈ Ine A, r s = 1 := (hr.unr_iff hart (Or.inr rfl) hA).2 hunr
  have hres : ∀ g : G M Ω, r (UpperTheory.V.Af.Bc.res K Ω M g) = 1 := by
    haveI : IsAlgClosure M Ω := by
      haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
      exact ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) M⟩
    obtain ⟨artM, hartM⟩ := GlobalTheory.globalArtinReciprocity_holds M Ω
    have hφc : Continuous (r.comp (UpperTheory.V.Af.Bc.res K Ω M)) :=
      hrc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K M Ω)
    have hbad : {w : HeightOneSpectrum (𝓞 M) | ¬ (η.UnrAt (HeightOneSpectrum.under (𝓞 K) w) ∧
        ∀ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f →
          η.val (HeightOneSpectrum.under (𝓞 K) w) ^ f = 1)}.Finite := by
      have h1 := GlobalTheory.QuadNormChar.tendsto_under (K := K) (K' := M)
      have h2 : ∀ᶠ w in Filter.cofinite, η.UnrAt (HeightOneSpectrum.under (𝓞 K) w) :=
        h1.eventually (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))
      exact Filter.eventually_cofinite.1 (h2.and hηev)
    have hone := GlobalTheory.FrobDense.eq_one_of_frob M Ω artM hartM (Qbar 2)ˣ (r.comp (UpperTheory.V.Af.Bc.res K Ω M)) hφc
      hbad.toFinset ?_
    · intro g
      exact DFunLike.congr_fun hone g
    · intro w hw A' hA' σ hσ
      rw [Set.Finite.mem_toFinset] at hw
      simp only [Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hwu, hwn⟩ := hw
      have hce : CharEig ι r (HeightOneSpectrum.under (𝓞 K) w)
          (η.val (HeightOneSpectrum.under (𝓞 K) w)) := by
        intro B hB
        refine ⟨(hr.unr_iff hart (Or.inr rfl) hB).2 hwu, fun σ' hσ' => ?_⟩
        have h3 := hr.frob_unr hart (Or.inr rfl) hwu hB hσ'
        rw [map_inv, Units.val_inv_eq_inv_val, h3, inv_inv]
        simp
      obtain ⟨-, hfr⟩ := UpperTheory.frobenius_power_compatibility K M Ω 2 ι w (w.asIdeal.inertiaDeg (𝓞 K))
        (GlobalTheory.QuadNormChar.normV_under w)
      obtain ⟨-, hval⟩ := hfr r _ hce A' hA'
      have h6 := hval σ hσ
      have h7 : ((η.val (HeightOneSpectrum.under (𝓞 K) w) : ℂˣ) : ℂ) ^
          (w.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hwn _ (GlobalTheory.QuadNormChar.normV_under w)]
        rfl
      rw [h7] at h6
      have h8 : (((r.comp (UpperTheory.V.Af.Bc.res K Ω M)) σ⁻¹ : (Qbar 2)ˣ) : Qbar 2) = 1 := by
        have h9 := congrArg ι.symm h6
        simpa using h9
      have h10 : (r.comp (UpperTheory.V.Af.Bc.res K Ω M)) σ⁻¹ = 1 := Units.ext h8
      rw [map_inv, inv_eq_one] at h10
      exact h10
  have hr1 : ∀ g : G K Ω, r g = 1 := by
    haveI : Fact (Nat.Prime (Module.finrank K M)) := ⟨hp⟩
    let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
    have hfix : ∀ g : G K Ω, ρ g = 1 → r g = 1 := by
      intro g hg
      let g' : Ω ≃ₐ[M] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
        have h1 := AlgEquiv.restrictNormal_commutes g M x
        have h2 : g.restrictNormal M = 1 := hg
        rw [h2] at h1
        simpa using h1.symm)
      have hg' : UpperTheory.V.Af.Bc.res K Ω M g' = g := by
        ext x
        rfl
      rw [← hg']
      exact hres g'
    have hρτ : ρ τ ≠ 1 := by
      intro h1
      apply hτM
      intro x
      have h3 := AlgEquiv.restrictNormal_commutes τ M x
      have h2 : τ.restrictNormal M = 1 := h1
      rw [h2] at h3
      simpa using h3.symm
    have hgen : Subgroup.zpowers (ρ τ) = ⊤ :=
      zpowers_eq_top_of_prime_card (p := Module.finrank K M)
        (IsGalois.card_aut_eq_finrank K M) hρτ
    intro g
    have hg : ρ g ∈ Subgroup.zpowers (ρ τ) := hgen ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hτ1 : r τ = 1 := hrI τ hτI
    have h4 : ρ ((τ ^ k)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have h5 := hfix _ h4
    rw [map_mul, map_inv, map_zpow, hτ1, one_zpow, inv_one, one_mul] at h5
    exact h5
  apply hη1
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
  have h := hr x σ hσ.symm
  rw [infPow_zero, lPow_zero, hr1 σ] at h
  simp only [Units.val_one, inv_one, mul_one] at h
  have h2 : ((η.1 x : ℂˣ) : ℂ) = 1 := by
    have h3 := congrArg ι h
    simpa using h3.symm
  ext
  simpa using h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormalOfComm
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open scoped commutatorElement

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem normal_of_comm {Γ : Type} [Group Γ] (H : Subgroup Γ) (h : commutator Γ ≤ H) : H.Normal := by
  constructor
  intro n hn g
  have hc : ⁅g, n⁆ ∈ H := h (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have he : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [he]
  exact H.mul_mem hc hn

open Polynomial in
private theorem exists_map_eq_conj_of_isAlgClosed_algebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsAlgebraic ℚ Ω]
    (φ : Ω →+* ℂ) (y : Ω) : ∃ z : Ω, φ z = starRingEnd ℂ (φ y) := by
  set p := minpoly ℚ y
  have hint : IsIntegral ℚ y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  set w := starRingEnd ℂ (φ y)
  have hw : aeval w p = 0 := by
    have h1 : aeval (φ.toRatAlgHom y) p = φ.toRatAlgHom (aeval y p) := Polynomial.aeval_algHom_apply _ _ _
    rw [minpoly.aeval, map_zero] at h1
    have h2 : aeval ((Complex.conjAe.toAlgHom.restrictScalars ℚ) (φ y)) p =
        (Complex.conjAe.toAlgHom.restrictScalars ℚ) (aeval (φ y) p) := Polynomial.aeval_algHom_apply _ _ _
    have h3 : aeval (φ y) p = 0 := h1
    rw [h3, map_zero] at h2
    exact h2
  set q := p.map (algebraMap ℚ Ω)
  have hq0 : q ≠ 0 := Polynomial.map_ne_zero hp0
  have hq := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := q))
  have hmap : q.map φ = p.map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hev := congrArg (fun P => (P.map φ).eval w) hq
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map,
    Function.comp_def, Polynomial.map_sub, Polynomial.map_X, eval_mul, eval_C, eval_multiset_prod,
    eval_sub, eval_X] at hev
  rw [hmap, eval_map, ← aeval_def, hw] at hev
  have hlc : φ q.leadingCoeff ≠ 0 := (map_ne_zero φ).mpr (leadingCoeff_ne_zero.mpr hq0)
  have hprod := (mul_eq_zero.mp hev).resolve_left hlc
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  exact ⟨r, (sub_eq_zero.mp hr).symm⟩

private theorem exists_algEquiv_map_eq_conj_of_exists_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (φ : Ω →+* ℂ) (hc : ∀ y : Ω, ∃ z : Ω, φ z = starRingEnd ℂ (φ y))
    (hF : ∀ a : F, starRingEnd ℂ (φ (algebraMap F Ω a)) = φ (algebraMap F Ω a)) :
    ∃ c : Ω ≃ₐ[F] Ω, ∀ x, φ (c x) = starRingEnd ℂ (φ x) := by
  choose c0 hc0 using hc
  have inj : Function.Injective φ := φ.injective
  let cf : Ω →ₐ[F] Ω :=
    { toFun := c0
      map_one' := inj (by rw [hc0, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hc0, map_mul, map_mul, map_mul, hc0, hc0])
      map_zero' := inj (by rw [hc0, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hc0, map_add (f := _), map_add (f := _), map_add (f := _), hc0, hc0])
      commutes' := fun a => inj (by rw [hc0, hF]) }
  exact ⟨AlgEquiv.ofBijective cf (Algebra.IsAlgebraic.algHom_bijective cf), fun x => hc0 x⟩

theorem exFld : ExFld := by
  intro E Ω _ _ _ _ _ _ H hH
  have hGE : IsGalois E Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Module.Finite (maximalRealSubfield E) E :=
    Module.Finite.of_restrictScalars_finite ℚ (maximalRealSubfield E) E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω := Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω
  haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩
  have hGF : IsGalois (maximalRealSubfield E) Ω := inferInstance
  have hopen : IsOpen ((H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) : Subgroup (G E Ω)) :
      Set (G E Ω)) :=
    hH.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom (maximalRealSubfield E) E Ω)
  set H' : Subgroup (G E Ω) := H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) with hH'
  have hclosed : IsClosed (H' : Set (G E Ω)) := Subgroup.isClosed_of_isOpen H' hopen
  have hcomm : commutator (G E Ω) ≤ H' := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [hH', Subgroup.mem_comap, map_commutatorElement]
    apply hH.comm
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  set M : IntermediateField E Ω := IntermediateField.fixedField H'
  have hfixM : M.fixingSubgroup = H' := InfiniteGalois.fixingSubgroup_fixedField ⟨H', hclosed⟩
  haveI hfin : FiniteDimensional E M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfixM]; exact hopen)
  haveI hgal : IsGalois E M :=
    (InfiniteGalois.normal_iff_isGalois M).mp (by rw [hfixM]; exact normal_of_comm H' hcomm)
  have hab : ∀ σ τ : Gal(M/E), σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω σ
    obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω τ
    have hk : ⁅g, h⁆ ∈ (AlgEquiv.restrictNormalHom (F := E) (K₁ := Ω) M).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hfixM]
      apply hcomm
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hk
    exact hk
  haveI : IsMulCommutative Gal(M/E) := ⟨⟨hab⟩⟩
  haveI : IsAbelianGalois E M := ⟨⟩
  haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E M }
  set KF : IntermediateField (maximalRealSubfield E) Ω := IntermediateField.fixedField H
  have hHclosed : IsClosed (H : Set (G (maximalRealSubfield E) Ω)) := Subgroup.isClosed_of_isOpen H hH.isOpen
  have hfixKF : KF.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hMeq : M = IntermediateField.adjoin E (KF : Set Ω) := by
    apply le_antisymm
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E (KF : Set Ω))]
      apply IntermediateField.fixedField_le
      intro g hg
      rw [hH', Subgroup.mem_comap, ← hfixKF, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x (IntermediateField.subset_adjoin _ _ hx)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (IntermediateField.mem_fixedField_iff H x).mp hx _ hg
  have hreal : ∀ x ∈ (KF : Set Ω), ∀ φ : Ω →+* ℂ, (φ x).im = 0 := by
    intro x hx φ
    obtain ⟨c, hc⟩ := exists_algEquiv_map_eq_conj_of_exists_conj (F := maximalRealSubfield E) φ (exists_map_eq_conj_of_isAlgClosed_algebraic φ) (fun a =>
      (mem_maximalRealSubfield_iff (a : E)).mp a.2 (φ.comp (algebraMap E Ω)))
    have hcH : c ∈ H := hH.real φ c hc
    have hcx : c x = x := (IntermediateField.mem_fixedField_iff H x).mp hx c hcH
    rw [← Complex.conj_eq_iff_im, ← hc, hcx]
  haveI hCM : IsCMField M := (GlobalTheory.CMSub.isCMField_sup_le_adjoin Ω E).2.2 M (KF : Set Ω) hreal hMeq
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) M⟩
  refine ⟨Fld.mk M, ?_⟩
  intro g
  constructor
  · intro h
    have hg : g ∈ M.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fun x hx => h ⟨x, hx⟩)
    rw [hfixM] at hg
    exact hg
  · intro h x
    have hg : g ∈ M.fixingSubgroup := by rw [hfixM]; exact h
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x.1 x.2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem isOpen_fixGrp (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra K Ω] [Algebra F K]
    [IsScalarTower F K Ω] [FiniteDimensional F K] : IsOpen (fixGrp F Ω K : Set (G F Ω)) := by
  let φ := IsScalarTower.toAlgHom F K Ω
  haveI : FiniteDimensional F φ.fieldRange := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  refine Subgroup.isOpen_mono (fun g hg x => ?_) φ.fieldRange.fixingSubgroup_isOpen
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem isAlgClosure_plus : IsAlgClosure (maximalRealSubfield E) Ω :=
  ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

theorem cuts_base : Cuts (Fld.base E Ω) ⊤ := fun g => ⟨fun _ => trivial, fun _ x => g.commutes x⟩

end

theorem noSelfTwist_of (h : NormRam) : NoSelfTwist :=
  fun K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp A v hA hτ a ha π B hB η hη =>
    GlobalTheory.TwistRamified.twist_ne K a ha π η v B hB (h K M Ω hp η hη A v hA hτ)

theorem quadraticCharTwist_of_exists_of_infinity (h1 : Quad0Ex) (h2 : InfOf) : Quad0 := by
  intro E Ω _ _ _ _ _ _ T hT
  refine h2 E Ω _ fun S hS => ?_
  obtain ⟨Q, ⟨δ, hδ, h3⟩, h4, u, hu, h5⟩ := h1 E Ω (T ∪ S) (hT.union hS)
  exact ⟨Q, ⟨⟨δ, hδ, fun t ht => h3 t (Or.inl ht)⟩, fun t ht => h4 t (Or.inl ht), u, fun h => hu (Or.inl h), h5⟩,
    u, fun h => hu (Or.inr h), h5⟩

theorem splitIso_holds : SplitIso := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ A v w hv hw h
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) M⟩
  obtain ⟨i, h1, -, h2, h3⟩ := PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift.exists_completionEquiv_of_he hv hw (fun σ => h _ (GlobalTheory.WeilDeligne.Weil_le_Dec hv σ.2))
    (GlobalTheory.InertFixVal.ramificationIdx_eq_one A v w hv hw fun σ hσ => h σ (Ine_le_Dec A hσ)).2
  exact ⟨i, h1, h2, h3⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.RealSpan
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.realSpan :
    RealSpan := by
  intro E M Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ g hE hR
  have hnot : ∃ e : E, algebraMap E M e ∉ maximalRealSubfield M := by
    by_contra h
    push_neg at h
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap E M))
    show ComplexEmbedding.conjugate _ = _
    ext x
    have := (mem_maximalRealSubfield_iff _).1 (h x) φ
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨e, he⟩ := hnot
  set α := algebraMap E M e with hα
  have h2 : Module.finrank (maximalRealSubfield M) M = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have htop : IntermediateField.adjoin (maximalRealSubfield M) {α} = ⊤ := by
    have hd := IntermediateField.finrank_dvd_of_le_right
      (le_top : IntermediateField.adjoin (maximalRealSubfield M) {α} ≤ ⊤)
    rw [IntermediateField.finrank_top', h2, Nat.dvd_prime Nat.prime_two] at hd
    rcases hd with hd | hd
    · rw [IntermediateField.finrank_eq_one_iff] at hd
      have hmem := IntermediateField.mem_adjoin_simple_self (maximalRealSubfield M) α
      rw [hd, IntermediateField.mem_bot] at hmem
      obtain ⟨y, hy⟩ := hmem
      exact absurd (hy ▸ y.2) he
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hd, IntermediateField.finrank_top', h2])
  intro x
  have hx : x ∈ IntermediateField.adjoin (maximalRealSubfield M) {α} := by
    rw [htop]
    exact IntermediateField.mem_top
  have hx' : x ∈ (IntermediateField.adjoin (maximalRealSubfield M) {α}).toSubfield := hx
  rw [IntermediateField.adjoin_toSubfield] at hx'
  have hle : Subfield.closure (Set.range (algebraMap (maximalRealSubfield M) M) ∪ {α}) ≤
      RingHom.eqLocusField ((g : Ω →+* Ω).comp (algebraMap M Ω)) (algebraMap M Ω) := by
    rw [Subfield.closure_le]
    rintro y (⟨z, rfl⟩ | hy)
    · exact hR z
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := hE e
      rw [IsScalarTower.algebraMap_apply E M Ω] at h1
      exact h1
  exact hle hx'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.RootMod
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_mem_asIdeal_of_normV_eq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    (hN : normV u = p) : ((p : 𝓞 F)) ∈ u.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hN]
  unfold Formalism.ConjugateSelfDual.normV
  simpa using card_nsmul_eq_zero' (G := 𝓞 F ⧸ u.asIdeal) (x := 1)

private theorem valuation_le_one_of_pow_eq_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (y : Ω) (n : ℕ) (hn : 0 < n)
    (h : y ^ n = 1) : A.valuation y ≤ 1 := by
  have h1 : A.valuation y ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_le_one_iff hn.ne').mp h1.le

private theorem not_valuation_natCast_lt_one_of_prime_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p n : ℕ) (hp : Nat.Prime p)
    (hpn : ¬ p ∣ n) (hvp : A.valuation (p : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro hvn
  have hc : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  have hb : ((Nat.gcd p n : ℤ)) = p * Nat.gcdA p n + n * Nat.gcdB p n := Nat.gcd_eq_gcd_ab p n
  rw [hc.gcd_eq_one] at hb
  have hb' : (1 : Ω) = (p : Ω) * (Nat.gcdA p n : Ω) + (n : Ω) * (Nat.gcdB p n : Ω) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hb
  have hA : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have h1 : A.valuation ((p : Ω) * (Nat.gcdA p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvp (hA _)
  have h2 : A.valuation ((n : Ω) * (Nat.gcdB p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvn (hA _)
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hb', map_one] at h3
  exact lt_irrefl _ h3

open Polynomial in
private theorem exists_zmod_castHom_eq_of_pow_char_eq_self {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (z : K)
    (hz : z ^ p = z) : ∃ k : ZMod p, (ZMod.castHom (dvd_refl p) K) k = z := by
  set f := ZMod.castHom (dvd_refl p) K
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [hcard] at this
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast hp.out.one_lt
  have hdeg : (X ^ p - X : (ZMod p)[X]).roots.card = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, Polynomial.natDegree_X_pow_sub_X hp.out.one_lt]
    simp [hcard]
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hdeg
  have hev := congrArg (fun P => (P.map f).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, eval_sub, eval_X, eval_C,
    eval_pow, hz, sub_self] at hev
  obtain ⟨w, -, hw0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)
  exact ⟨w, (sub_eq_zero.mp hw0).symm⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.rootMod :
    RootMod := by
  intro F Ω _ _ _ _ _ A u hu p hp hN y n hn hfix
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hu
  have hfy : σ y = y := hfix σ hσD
  have hvp : A.valuation (p : Ω) < 1 := by
    have h := (hu (p : 𝓞 F)).mpr (natCast_mem_asIdeal_of_normV_eq u p hN)
    simpa using h
  refine ⟨fun m hm => ?_, fun hprim hpn => ?_⟩
  · have hvy : A.valuation y ≤ 1 := by
      have h1 : A.valuation y ^ n ≤ 1 := by
        rw [← map_pow, hm]; exact valuation_natCast_le_one A m
      exact (pow_le_one_iff hn.ne').mp h1
    have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hvy
    set yA : A := ⟨y, hyA⟩
    set r := IsLocalRing.residue A
    have hp0 : ((p : IsLocalRing.ResidueField A)) = 0 := by
      rw [← map_natCast r, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simpa using hvp
    have hch : ringChar (IsLocalRing.ResidueField A) = p :=
      (hp.eq_one_or_self_of_dvd _ (ringChar.dvd hp0)).resolve_left (CharP.ringChar_ne_one)
    haveI := ringChar.of_eq hch
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hry : r yA ^ p = r yA := by
      have h0 : r (yA - yA ^ p) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        simpa using hlt
      rw [map_sub, map_pow, sub_eq_zero] at h0
      exact h0.symm
    obtain ⟨k, hk⟩ := exists_zmod_castHom_eq_of_pow_char_eq_self p (r yA) hry
    have hyn : yA ^ n = (m : A) := by
      apply Subtype.ext
      simpa using hm
    have hkm : (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (k ^ n) =
        (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (m : ZMod p) := by
      rw [map_pow, hk, ← map_pow, hyn, map_natCast, map_natCast]
    exact ⟨k, (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).injective hkm⟩
  · have hyn : y ^ n = 1 := hprim.pow_eq_one
    have hvy := valuation_le_one_of_pow_eq_one' A y n hn hyn
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hvn := not_valuation_natCast_lt_one_of_prime_not_dvd A p n hp hpn hvp
    have hyp : y = y ^ p := by
      refine eq_of_pow_eq_one A hvn hyn ?_ hlt
      rw [← pow_mul, mul_comm, pow_mul, hyn, one_pow]
    have hy0 : y ≠ 0 := hprim.ne_zero hn.ne'
    have hp1 : y ^ (p - 1) = 1 := by
      have h2 : y ^ (p - 1) * y = 1 * y := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_le]
        exact hyp.symm
      exact mul_right_cancel₀ hy0 h2
    exact hprim.dvd_of_pow_eq_one _ hp1
end

