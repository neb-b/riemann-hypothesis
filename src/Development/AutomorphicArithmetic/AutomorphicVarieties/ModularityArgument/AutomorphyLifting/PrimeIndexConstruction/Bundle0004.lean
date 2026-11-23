module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutomorphyRankFourPolarizedAlt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AutOf4W
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
theorem UpperTheory.V.Z.Win.Birth.autOf4W (hne : AlNe) :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok →
    Irr (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp T.G'.subtype) → Z.Win.Birth.OffW d.ι d.K' d.ρ (tenB d.ρ₁ d.τ) →
    Z.Win.Birth.AllW d.ι (Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp
      (resLe T.F_le)).toHomUnits ((toB d.δ).comp (resQ T.L))⁻¹) := by
  intro Ω _ _ _ l _ d T hT hok hirr hoff
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  have hatt := hoff T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwTw
section
theorem UpperTheory.V.Z.Win.Birth.awTw :
    UpperTheory.V.Z.Win.Birth.AwTw := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r κ hκ haut hW
  obtain ⟨_, art, χ, a, hart, -, hL⟩ := hκ
  obtain ⟨π, hreg, hatt⟩ := haut
  obtain ⟨t, ht⟩ := hW π hreg hatt
  obtain ⟨b, hb⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winTw F χ
  exact UpperTheory.V.Z.Win.Birth.awOne F Ω l n hn ι _ (π.twist χ)
    (UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL)
    ⟨t + b, fun v => hb n (by omega) π t v (ht v)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
section
open NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.LocLanglands Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af
open Neutral.B1 GlobalTheory.HeckeGal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem plainTor_tw {x : IrrGL (k := k)} (h : GlobalTheory.RoadU.PlainTor x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GlobalTheory.RoadU.PlainTor (x.tw χ hχ) := by
  obtain ⟨s, hs, h1, hu⟩ := h
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    exact h1 y' hy'
  · intro y hy z hz e
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.tw_nu] at e
    have hinv : IsSmoothChar χ⁻¹ := hχ.inv
    have e2 := congrArg (·.tw χ⁻¹ hinv) e
    simp only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one] at e2
    exact hu y' hy' z' hz' e2

end Local

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem plainAtR_twist {π : TR.CuspSub F n} {v : HeightOneSpectrum (𝓞 F)} (h : PlainAtR π v) (χ : HChar F) :
    PlainAtR (π.twist χ) v := by
  intro σ hσ
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one]
  have h1 := hσ.twist χ⁻¹
  rw [e] at h1
  have h2 := h _ h1
  have hsm := GlobalTheory.HeckeComp.smooth_loc χ⁻¹ v
  have hsm' := GlobalTheory.HeckeComp.smooth_loc χ v
  have h3 : IrrGL.of (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).ρ
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).smooth
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).irred =
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ⁻¹.loc v) hsm :=
    (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ hsm).symm
  rw [h3] at h2
  have h4 := plainTor_tw h2 (χ.loc v) hsm'
  rw [IrrGL.tw_tw] at h4
  have e3 : χ⁻¹.loc v * χ.loc v = 1 := MonoidHom.ext fun x => by
    change (χ.loc v x)⁻¹ * χ.loc v x = 1
    simp
  have key : ∀ (c : (v.adicCompletion F)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 →
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw c hc = IrrGL.of σ.ρ σ.smooth σ.irred := by
    rintro _ hc rfl
    exact IrrGL.tw_one _ _
  rwa [key _ _ e3] at h4

end UpperTheory.V.Z.Win.Birth

theorem UpperTheory.V.Z.Win.Birth.prTw :
    UpperTheory.V.Z.Win.Birth.PrTw := by
  rintro F Ω _ _ _ _ _ _ l _ ι r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA, hP⟩
  have expo_intR : ∀ v : InfinitePlace F, ∃ k : ℤ, TR.expo χ v = k := by
    let diagR : F →+* TR.Rinf F :=
      (TR.pInf F).comp (algebraMap F (Ad F))

    have infDiag_eqR (k : Fˣ) : infDiag k = TR.infId F (Units.map diagR.toMonoidHom k) := by
      classical
      have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
        unfold infDiag
        rw [MonoidHom.finsetProd_apply, Units.coe_prod]
        let infIncl : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
          MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        change ∏ w : InfinitePlace F, infIncl (Pi.mulSingle w (algebraMap F w.Completion k)) =
          infIncl (fun w => algebraMap F w.Completion k)
        rw [← map_prod, Finset.univ_prod_mulSingle]
      apply Units.ext
      rw [h]
      refine Prod.ext ?_ ?_
      · change _ = 1 - TR.infEq F 1 + TR.infEq F ((TR.infEq F).symm (algebraMap F (InfiniteAdeleRing F) k))
        simp
      · change (1 : Af F) = 1 - 0 + 0
        simp

    have denseRange_diagR : DenseRange diagR := by
      have hc : Continuous (TR.infEq F).symm := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      exact (TR.infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

    have denseRange_unitsR : DenseRange (Units.map diagR.toMonoidHom) := by
      refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
      obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
      have h0 : k ≠ 0 := by
        rintro rfl
        exact v.ne_zero (hk.trans (map_zero _))
      exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

    have diagR_mk (φ : F →+* ℂ) (k : F) : ((diagR k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
      have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
      have e : diagR k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
        change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr
          (algebraMap F (InfinitePlace.mk φ).Completion k) = _
        rw [AbsoluteValue.Completion.algebraMap_def]
        simp [WithAbs.algebraMap_right_apply]
      rw [e, InfinitePlace.embedding_of_isReal_apply,
        InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

    have chiInf_pos (u : (TR.Rinf F)ˣ)
        (hu : ∀ v, 0 < u.val v) :
        ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : F →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ a φ := by
      have hc : ∀ v, Continuous fun u : (TR.Rinf F)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
      have ho : IsOpen {u : (TR.Rinf F)ˣ | ∀ v, 0 < u.val v} := by
        rw [Set.ofPred_forall]
        exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
      have hcl : IsClosed {u : (TR.Rinf F)ˣ |
          ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : F →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ a φ} :=
        isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
          (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
            (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
      refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
      rintro _ ⟨hk, k, rfl⟩
      have h1 := hχ k fun φ => by
        have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
        have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : F)
        exact h2.trans_eq (Complex.ofReal_injective h3)
      rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
      refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
      exact congrArg (· ^ a φ) (diagR_mk φ (k : F)).symm

    intro v
    classical
    refine ⟨∑ φ : F →+* ℂ, if InfinitePlace.mk φ = v then a φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
    rw [chiInf_pos _ fun w => Real.exp_pos _]
    simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
    rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
    refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
    split_ifs with e
    · rw [e, Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne e]

  have hAtt : AttR ι (tw r κ) (π.twist χ) := by
    have ev_notMem :
        ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by
      have hl : l.Prime := Fact.out
      have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast hl.ne_zero
      refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
      exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    change AttachedSys ι r π.HasSat at hA
    refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ 2 r).2.2 κ hA.1, ?_⟩
    filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ), ev_notMem]
      with w ⟨B, hB, hE⟩ hu hl
    refine ⟨_, hB.twist hu, ?_⟩
    have hc : UpperTheory.V.Af.Bc.CharEig ι κ w (χ.val w : ℂ) := by
      refine fun A hOver => ⟨(hL.unr_iff ha (Or.inl hl) hOver).2 hu, fun σ hσ => ?_⟩
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inl hl) hu hOver hσ, inv_inv, RingEquiv.apply_symm_apply]
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι 2 r κ w _ _ hE hc
    convert h4 using 1
    simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  refine ⟨π.twist χ, hr.twist expo_intR, hAtt, fun v => ?_⟩
  rcases hP v with h | ⟨B, hB⟩
  · exact Or.inl (plainAtR_twist h χ)
  · by_cases hu : χ.UnrAt v
    · exact Or.inr ⟨_, hB.twist hu⟩
    · exact Or.inl (plainAtR_twist (plainAtR_of_hasSat (by norm_num) π v B hB) χ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N UpperTheory.V UpperTheory.V.Sd

theorem UpperTheory.V.Z.Win.Birth.potOrd :
    UpperTheory.V.Z.Win.Birth.PotOrd := by
  intro F Ω _ _ _ _ _ l _ n r m ψ κ hm H v hv
  have hp : UpperTheory.V.Z.Win.PotUnl r v := by
    refine UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfFlag F Ω l n r m hm v hv fun A hA => ?_
    have hAl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 F)).2 hv
      simpa only [map_natCast] using h1
    obtain ⟨c, hflag, hc, -⟩ := H A hAl
    exact ⟨c, 1, one_pos, hflag, fun i s hs => by rw [pow_one, pow_one]; exact hc i s hs⟩
  exact ((((UpperTheory.V.Z.Win.flagLaws F Ω l n r).2.1 κ).2.2 v).2).1 hp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ValIffMem
section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem val_iff_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← hA]
  simp

private theorem prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 F ⧸ v.asIdeal), CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem UpperTheory.V.Z.Win.Birth.badOfW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.SplitOfDec → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.UnrOfIne → SphOfUnrW → BadOfW := by
  intro hS hU hP Ω _ _ _ l _ ι K' L M _ _ _ _ _ _ _ hM ρ r π hG hr hpol hreg hatt hW hun v hv
  have hMfix : ∀ s : G L Ω, resQ L s ∈ K'.fixingSubgroup → ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := fun s hs x => by
    have : resQ L s ∈ M.fixingSubgroup := by
      rw [hM, IntermediateField.fixingSubgroup_sup]
      exact ⟨hs, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
  obtain ⟨p, hp, hpv⟩ := prime_mem v
  rcases hG p hp with h | ⟨hpl, h⟩
  · exact absurd (hS L M Ω v fun A hA s hs => hMfix s (h A ((val_iff_mem hA p).2 hpv) hs)) hv
  refine ⟨hU L M Ω v fun A hA s hs => hMfix s (h A ((val_iff_mem hA p).2 hpv) s hs).1, fun w hw => ?_⟩
  have hpw : ((p : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    rw [← hw] at hpv
    change algebraMap (𝓞 L) (𝓞 M) p ∈ w.asIdeal at hpv
    rwa [map_natCast] at hpv
  have hlw : ((l : ℕ) : 𝓞 M) ∉ w.asIdeal := fun hl => by
    have hc : IsCoprime ((p : ℕ) : 𝓞 M) ((l : ℕ) : 𝓞 M) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp Fact.out).2 hpl)
    obtain ⟨a, b, e⟩ := hc
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hpw) (w.asIdeal.mul_mem_left b hl)))
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  refine hP M Ω l ι 2 one_le_two r π hr hpol hreg hatt hW w hlw A hA fun s hs => ?_
  exact hun A (mt (val_iff_mem hA l).1 hlw) s hs (h A ((val_iff_mem hA p).2 hpw) (galEmb L M Ω s) ⟨hs.1, hs.2⟩).2
end

