module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.AllLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem dec_restrict {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {g : G K Ω} (hg : g ∈ Dec (F := K) A) :
    AlgEquiv.restrictScalars F g ∈ Dec (F := F) A :=
  GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec hg x

private def Carry {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ)
    [Fact l.Prime] (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E))) (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) : Prop :=
  ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
    UpperTheory.Gal.InertialTypesAlt.Lifts (UpperTheory.Gal.InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : UpperTheory.Gal.InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
    (∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))) ∧
    ∀ u ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A u → (∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) →
      ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → ∃ B, (CG.mk P).HasSat w' B

theorem UpperTheory.Gal.NearKilling.allLift :
    StepLift → UpperTheory.Gal.UnramifiedFromSplittingCriterion.SatSplit → AllLift := by
  intro hStep hSat E Ω _ _ _ _ _ _ l a _ ha π χ hχ S hS X hX
  suffices H : Carry l a π S X by
    obtain ⟨P, χ', h1, h2, h3, -⟩ := H
    exact ⟨P, χ', h1, h2, h3⟩
  refine UpperTheory.Gal.UnramifiedFromSplittingCriterion.Tower.induction (S := S) (P := Carry l a π S) ?_ ?_ hX
  · refine ⟨π, χ, Relation.ReflTransGen.refl, hχ, fun ι r h => ?_, fun u hu A hA _ w' hw' => ?_⟩
    · exact h
    · have e : w' = u := HeightOneSpectrum.ext (Ideal.ext fun x => (hw' x).symm.trans (hA x))
      rw [e]
      exact hS u hu
  · rintro X Y - ⟨alg, t1, t2, hG, hp, u, hu, hsp, A, hA, τ, hτ, hτn⟩ ⟨P, χ', h1, h2, h3, h4⟩
    obtain ⟨v, hv, -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E X.K Ω A u hA
    have hfix : ∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg =>
      (hsp A hA (AlgEquiv.restrictScalars _ g) (dec_restrict hg)).2
    obtain ⟨P', χ'', hbc, hsl, hsc, -, hweak⟩ :=
      hStep X.K Y.K Ω hp l a ha P χ' h2 A v hv ⟨τ, hτ, hτn⟩ (h4 u hu A hA hfix v hv)
    refine ⟨P', χ'', Relation.ReflTransGen.tail h1 ⟨alg, t2, hG, hp, hbc⟩, hsc, fun ι r h => ?_, ?_⟩
    · exact hweak ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K)) (h3 ι r h)
    · intro u' hu' A' hA' hfix' w' hw'
      have hv' : IsPlaceOver A' (w'.under (𝓞 X.K)) := fun x => by
        rw [IsScalarTower.algebraMap_apply X.K Y.K Ω]
        exact hw' (algebraMap (𝓞 X.K) (𝓞 Y.K) x)
      have hfixX : ∀ g ∈ Dec (F := E) A', UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg x => by
        have := hfix' g hg (algebraMap X.K Y.K x)
        rwa [← IsScalarTower.algebraMap_apply] at this
      obtain ⟨B, hB⟩ := h4 u' hu' A' hA' hfixX _ hv'
      exact ⟨B, hSat X.K Y.K Ω A' _ w' hv' hw' (fun g hg => hfix' _ (dec_restrict hg)) a P P' hsl B hB⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.PolNorm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem pol_norm (hjs : GlobalTheory.Published.JacquetShalikaRigidity) (hgk : GlobalTheory.Published.GelfandKazhdanDual)
    (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M]
    [IsCMField M] [Algebra K M] (a : ℕ) (ha : 1 ≤ a) (π : CuspSub K a) (π' : CuspSub M a) (χ : HChar (maximalRealSubfield K))
    (hpol : GlobalTheory.ContraPair.PolarizedPair π χ) (hbc : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk π').HasSat) :
    ∃ χ' : HChar (maximalRealSubfield M), GlobalTheory.ContraPair.PolarizedPair π' χ' ∧
      ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  obtain ⟨χ', hs, hN⟩ := _root_.GlobalTheory.RealNormChar.main K M a χ hpol.sign
  refine ⟨χ', ⟨hs, ?_⟩, hN⟩
  apply UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hjs hgk M a ha π' (compNorm M χ')

  have hT := GlobalTheory.PolarizedSat.hasSat_conjPlace GlobalTheory.automorphicFormsFiniteGL K a π χ hpol
  have hU : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (compNorm K χ).UnrAt v :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hT' := _root_.GlobalTheory.eventually_cofinite_under_of_eventually_cofinite K M _ (hT.and hU)
  have hbc' := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite.eventually hbc
  filter_upwards [hT', hbc, hbc'] with w ⟨hTw, hUw⟩ hw hcw
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.AboveL.ResDeg.normV_eq_under_pow K M w
  obtain ⟨hu', hval⟩ := _root_.GlobalTheory.NormValGen.unrAt_val_of_comp_norm K M (compNorm K χ) (compNorm M χ') hN w f hf hUw
  refine ⟨hu', ?_⟩
  obtain ⟨B, hB1, hB2⟩ := hw f hf
  have hcu := _root_.GlobalTheory.ConjUnder.cPl_under K M w
  have hnc : normV (UpperTheory.V.Af.Bc.cPl w) = normV ((UpperTheory.V.Af.Bc.cPl w).under (𝓞 K)) ^ f := by
    rw [hcu]
    have e1 : normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
      simpa only [normV, ← Ideal.absNorm_eq_natCard, UpperTheory.V.Af.Bc.cPl] using GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (IsCMField.complexConj M).toRingEquiv w
    have e2 : normV (UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K))) = normV (w.under (𝓞 K)) :=
      by simpa only [normV, ← Ideal.absNorm_eq_natCard, UpperTheory.V.Af.Bc.cPl] using GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (IsCMField.complexConj K).toRingEquiv (w.under (𝓞 K))
    rw [e1, e2, hf]
  obtain ⟨C, hC1, hC2⟩ := hcw f hnc
  rw [hcu] at hC1
  have e := _root_.GlobalTheory.AboveL.cg_hasSat_unique K a (CG.mk π) _ _ _ hC1 (hTw B hB1)
  refine ⟨_, _, hB2, hC2, ?_⟩
  rw [e, hval]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, mul_pow, inv_pow, mul_inv, inv_inv]

theorem UpperTheory.Gal.NearKilling.polBC :
    GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual → PolBC := by
  intro hjs hgk K M _ _ _ _ _ _ _ a ha π P χ hpol hbc
  obtain ⟨χ', hχ', hN⟩ := pol_norm hjs hgk K M a ha π P χ hpol hbc
  refine ⟨⟨χ', hχ'⟩, fun hq => ?_⟩
  have h1 : compNorm M χ' = 1 := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    rw [hN x, hq, map_pow, compNorm_quadChar, one_pow]
    rfl
  refine ⟨fun v => ?_, ?_⟩
  · have e : (quadChar M ^ a).locInf v (-1) = (quadChar M).locInf v (-1) ^ a := rfl
    rw [e, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow]
    have h := hχ'.dual
    rwa [h1] at h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.StepLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.stepLift :
    UpperTheory.V.Z.Bc.CBCc → UpperTheory.Gal.UnramifiedFromSplittingCriterion.NoSelfTwist → PolBC → WeakRes → StepLift := by
  intro hC hN hP hW K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l a _ ha π χ hs A v hv hτ hsat
  obtain ⟨hreg, hpol, -⟩ := hs
  have hK : IsTotallyComplex K := inferInstance
  have hM : IsTotallyComplex M := inferInstance
  rcases (hC K M hp hK a ha).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨Q, hw, hinf, hsplit⟩
  · exfalso
    obtain ⟨B, hB⟩ := hsat
    refine hN K M Ω hp A v hv hτ a ha (CG.mk π) B hB η hη ?_
    rw [CG.twist_mk]
    exact Quotient.sound hi
  · cases Q with
    | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim
    | cx P =>
      have hw' : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := hw
      obtain ⟨⟨χ', hχ'⟩, hq⟩ := hP K M a ha π P χ hpol hw'
      refine ⟨P, χ', hw, hsplit, ⟨?_, hχ', trivial⟩, hq, fun ι r hr => hW K M Ω l ι a π P hw' r hr⟩
      refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
      have h1 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M))
      have h2 : P.HasInfChar τ ((CG.mk π).infChar (τ.comp (algebraMap K M))) := hinf τ _ h1
      have h3 : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M)) :=
        CG.HasInfChar.infChar_eq h2
      rw [h3]
      exact hreg _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.WeakRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

open GlobalTheory.WeakBaseChange in
theorem UpperTheory.Gal.NearKilling.weakRes :
    WeakRes := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (UpperTheory.V.Af.Bc.res E Ω M).range with hH
    haveI : (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)) ?_
    have hrange : ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (UpperTheory.V.Af.Bc.res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · unfold UpperTheory.V.Published.WeakBC at hL
    filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt, hL] with w h hW
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    obtain ⟨B', hB', hP⟩ := hW f h2
    have hBB : B' = B := _root_.GlobalTheory.AboveL.cg_hasSat_unique E a (CG.mk π) (w.under (𝓞 E)) B' B hB' hB
    subst hBB
    refine ⟨B'.map (· ^ f), hP, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
end

