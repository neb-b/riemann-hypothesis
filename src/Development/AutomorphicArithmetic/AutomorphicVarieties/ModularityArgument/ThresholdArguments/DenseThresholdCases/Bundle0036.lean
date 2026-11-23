module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ExistsPrimeIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumberU3US
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyDescentSolvableCMToImaginaryQuadraticA
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr (H : _root_.UpperTheory.V.Af.HypothesesH') (hS : SolC) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L] (hle : K ≤ L)
    (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (hn : 1 ≤ n) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r) (hθ : IsAlgChar ι θ)
    (hd : DualTw r θ) (hirr : IsIrr (r.comp (resG ℚ L Ω))) (haut : IsAut ι (r.comp (resG ℚ L Ω))) : IsAutomorphicOverImagQuad ι r := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.comp (resG ℚ K Ω)).comp (resG K L Ω) = r.comp (resG ℚ L Ω) := rfl
  have i2 : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K L Ω)) := e ▸ hirr
  have i1 : IsIrr (r.comp (resG ℚ K Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ i2
  have hconj : ∃ c : G ℚ Ω, IsConjEl c := by
    have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let j : Ω →ₐ[ℚ] ℂ := _root_.IsAlgClosed.lift
    let E : IntermediateField ℚ ℂ := j.fieldRange
    let e : Ω ≃ₐ[ℚ] E := AlgEquiv.ofInjectiveField j
    have : Normal ℚ E := Normal.of_algEquiv e
    let f : E →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom.comp E.val
    let g : E ≃ₐ[ℚ] E := f.restrictNormal' E
    have hg (y : E) : (g y : ℂ) = starRingEnd ℂ (y : ℂ) :=
      f.restrictNormal_commutes E y
    have he (x : Ω) : (e x : ℂ) = j x := rfl
    refine ⟨e.trans (g.trans e.symm), j.toRingHom, fun x => ?_⟩
    show j (e.symm (g (e x))) = starRingEnd ℂ (j x)
    rw [← he, AlgEquiv.apply_symm_apply, hg, he]
  obtain ⟨c, hc⟩ := hconj
  obtain ⟨P, hP⟩ := id hd
  have hp : IsPairing c (r.comp (resG ℚ K Ω)) (θ.comp (resG ℚ K Ω)) (P * r c⁻¹) := fun s s' h => by
    have h' : resG ℚ K Ω s' = c * resG ℚ K Ω s * c⁻¹ := h
    have e0 : r c⁻¹ * r (resG ℚ K Ω s') = r (resG ℚ K Ω s) * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
    have e' := congrArg Units.val e0
    have h1 := hP (resG ℚ K Ω s)
    simp only [Units.val_mul, MonoidHom.comp_apply] at e' ⊢
    rw [← Matrix.smul_mul, ← h1]
    simp only [Matrix.mul_assoc, e']
  refine _root_.UpperTheory.GalN.V.ofOne0_alt H third (_root_.UpperTheory.V.Z.Bc.across_alt H hS biQuad) K Ω hK l ι n hn r θ hθ hd i1 ?_
  exact (hS ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance inferInstance l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) i2 hθ (Ws.auSign _) ⟨c, _, hc, hp⟩).2 (e ▸ haut)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpSol
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT
private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp
private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }
private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (ha : IsAutC ι r) (hi : IsIrr (r.comp (galEmb F E Ω))) :
    IsAutC ι (r.comp (galEmb F E Ω)) := by
  obtain ⟨π, hreg, -, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
open UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Bc.upSol_of_alt (hA : _root_.UpperTheory.V.Af.Hypotheses') (cyc : UpperTheory.V.Z.Bc.CycC) : UpperTheory.V.Sd.UpSol := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r hc ha hi
  by_cases h1 : Module.finrank F E = 1
  · exact up_one F E Ω h1 l ι n r ha hi
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := closure_tower K E Ω
  haveI : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom F) (AlgEquiv.restrictScalars_injective F)
  have hdeg : Module.finrank F K = M.index := by
    have h2 := Module.finrank_mul_finrank F K E
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F E, ← M.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hlt : Module.finrank K E < d := by
    rw [← hd, ← Module.finrank_mul_finrank F K E, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
  have e : r.comp (galEmb F E Ω) = (r.comp (galEmb F K Ω)).comp (galEmb K E Ω) := rfl
  rw [e] at hi ⊢
  refine ih _ hlt K rfl _ (hc.comp (resFacts F K Ω l n r).1) ?_ hi
  exact _root_.UpperTheory.V.Z.Bc.upCyc_of_alt hA cyc F K Ω l ι (hdeg ▸ hp) n hn r hc ha ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ hi)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainRankFourGood
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.J.unramified_algebraic_weights : _root_.UpperTheory.V.J.UnramifiedEndsStatement := _root_.UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series (unrAlgE unrAlgW muRange)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FPropGKU
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J
private theorem isCM (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) (h' : IsTotallyComplex K) :
    IsCMField K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h }
  exact IsCMField.ofCMExtension ℚ K
private theorem exists_w (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal := by
  have h1 : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    have := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at this
    rcases Nat.pow_eq_one.1 this with h | h
    · exact hp.ne_one h
    · exact Module.finrank_pos.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h1
  have hm : (p : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hm⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))
private theorem cop_norm {K : Type} [Field K] [NumberField K] {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) : (normV w).Coprime N := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [Ideal.absNorm_span_natCast] at h
  rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact Nat.Coprime.coprime_dvd_left h (((Nat.Prime.coprime_iff_not_dvd hp).2 hN).pow_left _)
private theorem frob_val {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [hl : Fact l.Prime] {p N : ℕ} [NeZero N] (hp : p.Prime) (hN : ¬ p ∣ N) (hlp : l ≠ p)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    {σ : G K Ω} (hσ : IsFrob B (normV w) σ) :
    ((Chr.cls ℚ Ω N (galEmb ℚ K Ω σ) : (ZMod N)ˣ) : ZMod N) = normV w ∧
      ((cycZ ℚ Ω l (galEmb ℚ K Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = normV w := by
  obtain ⟨-, -, -, hcop, -, -, hpow, -⟩ := ML.placeBasic Ω
  have hp' : ML.Over B p := by
    have := (hB p).2 hw
    simpa only [map_natCast] using this
  constructor
  · have hφ : IsFrob (F := ℚ) B (normV w) (galEmb ℚ K Ω σ) :=
      ⟨Subgroup.mem_comap.1 (((galEmbFam ℚ K Ω l).1 B).1.ge hσ.1), hσ.2⟩
    have h := hpow B _ N _ hφ (hcop B p N ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hp')
    rw [(Chr.clsFacts ℚ Ω N).2.2.1 _ (ZMod.unitOfCoprime _ (cop_norm hp hN hw)) fun ζ hζ => ?_, ZMod.coe_unitOfCoprime]
    rw [h ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  · refine cycZ_of_isFrob (F := K) (fun h => ?_) hB hσ
    refine hcop B p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hp' ?_
    have := (hB l).2 h
    simpa only [map_natCast] using this
private theorem vl_bound {l : ℕ} [hl : Fact l.Prime] {ι : Type} {κ : Type} [Fintype ι] (X : ι → Finset κ)
    (f : ι → κ → PadicAlgCl l) (NN : ℤ) (h0 : NN ≠ 0) (hf : ∀ o, ∀ ρ ∈ X o, f o ρ ≠ 0)
    (h : ‖((NN : ℤ) : PadicAlgCl l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖f o ρ‖) :
    ∑ o, ∑ ρ ∈ X o, vl l (f o ρ) ≤ padicValInt l NN := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have e1 : ‖((NN : ℤ) : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℝ)) := by
    rw [← map_intCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends,
      Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_intCast, ← Real.rpow_intCast]
    simp
  have h2 := Real.logb_le_logb_of_le hl1 (by rw [e1]; positivity) h
  rw [e1, Real.logb_rpow (by positivity) hl1.ne', Real.logb_prod _ _ fun o _ =>
    Finset.prod_ne_zero_iff.2 fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ),
    Finset.sum_congr rfl fun o _ => Real.logb_prod _ _ fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ)] at h2
  simp only [vl, Finset.sum_neg_distrib]
  linarith
private theorem ker_comp {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    (ψ : DirichletCharacter O N) : (ψ.ringHomComp f).toUnitHom.ker = ψ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, Units.val_one]
  exact map_eq_one_iff f hf
private theorem card_orb {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    Nat.card {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} ≤ Nat.totient H.index := by
  by_cases h : ∃ χ : DirichletCharacter ℂ N, χ.toUnitHom.ker = H
  · obtain ⟨χ, rfl⟩ := h
    obtain ⟨h1, -, -, h2⟩ := orbFacts ℂ N χ
    rw [h1, ← h2]
    exact le_rfl
  · haveI : IsEmpty {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := ⟨fun x => h ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
private theorem t_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e q : ℕ) (ψ : DirichletCharacter c.O N) (ι : Qbar l ≃+* ℂ) (g : G ℚ Ω)
    (h1 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = q) (h2 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = q) :
    ι.symm (Af.eis3 q e (ι (algebraMap c.O (PadicAlgCl l) (ψ q)))⁻¹) =
      algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹ : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹)⁻¹ : c.Oˣ) : c.O)) := by
  have e1 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.Oˣ) : c.O) = (q : c.O) ^ e * ψ q := by
    simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  rw [map_inv (Chr.Psi l e (Chr.dirG ℚ Ω ψ)), inv_inv, map_add (f := _), map_add (f := _), map_one, map_units_inv, e1]
  simp [Af.eis3, mul_comm]
private theorem comp_inj {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    {ψ ψ' : DirichletCharacter O N} (h : ψ.ringHomComp f = ψ'.ringHomComp f) : ψ = ψ' :=
  MulChar.ext' fun a => hf (by rw [← MulChar.ringHomComp_apply, h, MulChar.ringHomComp_apply])
private theorem orb_equiv {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) (f : c.O →+* ℂ)
    (hf : Function.Injective f) {ψ₀ : DirichletCharacter c.O N} (h₀ : ψ₀ ∈ orb c H) :
    ∃ E : orb c H ≃ {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H}, ∀ ψ, (E ψ).1 = ψ.1.ringHomComp f := by
  refine ⟨Equiv.ofBijective (fun ψ => ⟨ψ.1.ringHomComp f, (ker_comp f hf _).trans ((mem_orb c).1 ψ.2)⟩) ⟨?_, ?_⟩,
    fun _ => rfl⟩
  · intro a b h
    exact Subtype.ext (comp_inj f hf (congrArg Subtype.val h))
  · rintro ⟨χ, hχ⟩
    have h1 := (ker_comp f hf ψ₀).trans ((mem_orb c).1 h₀)
    obtain ⟨j, -, hj⟩ := ((orbFacts ℂ N (ψ₀.ringHomComp f)).2.2.1 χ).1 (hχ.trans h1.symm)
    rw [MulChar.ringHomComp_pow] at hj
    refine ⟨⟨ψ₀ ^ j, (mem_orb c).2 ?_⟩, Subtype.ext hj.symm⟩
    rw [← ker_comp f hf, ← hj, hχ]
theorem UpperTheory.V.Z.J.propGK_of_numberU3U_of_oneCharU :
    _root_.UpperTheory.V.Z.J.NumberU3U_s → _root_.UpperTheory.V.Z.J.OneCharU_s → PropGK := by
  intro hNum hOne K _ _
  by_cases hK : Module.finrank ℚ K = 2 ∧ IsTotallyComplex K
  swap
  · refine ⟨0, 0, fun e N _ H p _ _ _ => ⟨1, one_ne_zero, by simp, fun Ω _ _ _ _ l _ _ c h => ?_⟩⟩
    obtain ⟨ψ, -, hψ⟩ := h
    exact absurd ⟨hψ.quad, hψ.imag⟩ hK
  haveI := isCM K hK.1 hK.2
  obtain ⟨c₅, A, hC⟩ := hNum K hK.1
  refine ⟨c₅, A, fun e N _ H p he hp hnd => ?_⟩
  have hN : ¬ p ∣ N := fun h => hnd ((h.mul_left 30).mul_right _)
  have hd : ¬ (p : ℤ) ∣ discr K := fun h => hnd ((Int.natCast_dvd.1 h).mul_left _)
  have h7 : 7 ≤ p := by
    have h30 : ¬ p ∣ 30 := fun h => hnd ((h.mul_right N).mul_right _)
    by_contra h
    push Not at h
    clear hnd hN hd
    revert hp h30
    interval_cases p <;> decide
  obtain ⟨w, hw⟩ := exists_w K hp
  haveI : Fintype {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := Fintype.ofFinite _
  obtain ⟨NN, h0, hsz, hdiv⟩ := hC e he N (NeZero.pos N) p w hp hw h7 hN hd
    {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} (fun χ => (χ.1 (normV w))⁻¹)
    (fun χ => ⟨orderOf χ.1, orderOf_pos _, by
      rw [inv_pow, ← ZMod.coe_unitOfCoprime _ (cop_norm hp hN hw), ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply_coe, inv_one]⟩)
    (fun σ => ⟨⟨fun χ => ⟨χ.1.ringHomComp σ.toRingHom, (ker_comp _ σ.injective _).trans χ.2⟩,
      fun χ => ⟨χ.1.ringHomComp σ.symm.toRingHom, (ker_comp _ σ.symm.injective _).trans χ.2⟩,
      fun χ => Subtype.ext (MulChar.ext' fun a => σ.symm_apply_apply _),
      fun χ => Subtype.ext (MulChar.ext' fun a => σ.apply_symm_apply _)⟩, fun χ => (map_inv₀ σ _).symm⟩)
  refine ⟨NN, h0, hsz.trans ?_, fun Ω _ _ _ _ l hl hlp c h => ?_⟩
  · have := card_orb H
    rw [Nat.card_eq_fintype_card] at this
    have hl := Real.log_natCast_nonneg p
    gcongr
  obtain ⟨ψ₀, h₀, hψ₀⟩ := h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hB
  have hD := hdiv l hψ₀.l_odd hlp Ω ι B hB σ hσ
  obtain ⟨E, hE⟩ := orb_equiv c H (ι.toRingHom.comp (algebraMap c.O (PadicAlgCl l)))
    (ι.injective.comp Subtype.val_injective) h₀
  obtain ⟨f1, f2⟩ := frob_val hp hN hlp hw hB hσ
  have key := fun ψ : orb c H => hOne Ω K l c N e ψ.1
    ((gdFacts Ω K l e c.O N ψ₀ hψ₀).2.2.2.2.2.2.2 ψ.1 (((mem_orb c).1 ψ.2).trans ((mem_orb c).1 h₀).symm)).1 ι σ⁻¹
    (ι.symm (Af.eis3 (normV w) e ((E ψ).1 (normV w))⁻¹))
    (by rw [hE, map_inv (galEmb ℚ K Ω)]; exact t_eq c e _ ψ.1 ι _ f1 f2)
    (fun ρ hρ => (hD (fun _ => {ρ}) (fun _ ρ' h => by rwa [Finset.mem_singleton.1 h])
      (fun _ a ha b hb _ => (Finset.mem_singleton.1 ha).trans (Finset.mem_singleton.1 hb).symm)).1 (E ψ) ρ
      (Finset.mem_singleton_self ρ))
  refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, ?_⟩
  choose X hX1 hX2 hX3 using fun ψ => (key ψ).2
  obtain ⟨hne, hle⟩ := hD (fun o => X (E.symm o)) (fun o => hX1 _) (fun o => hX2 _)
  have hb := vl_bound _ _ NN h0 (fun o ρ hρ => sub_ne_zero.2 (hne o ρ hρ)) hle
  rw [← Finset.sum_coe_sort]
  refine (Finset.sum_le_sum fun ψ _ => hX3 ψ).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hb) zero_le_two
  exact Fintype.sum_equiv E _ _ fun ψ => by rw [E.symm_apply_apply]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuPolG
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT :
    _root_.UpperTheory.V.Af.HypothesesH' → RowT → PolG := by
  intro PH hRow E Ω _ _ _ _ _ _ l _ ι a ha P χ hreg hpol σ hσ
  obtain ⟨r, wt, HT, H⟩ := hRow E Ω l ι a ha P χ hreg
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a P (compNorm E χ) (PH.toClassicalTheorems.litN.aut.gk E a _) hpol.dual⟩
  have hRc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w hg A h O _ _ _ Bw hj => ?_,
    fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj g => ?_⟩⟩, H.weights⟩
  · obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w h
    obtain ⟨g1, g2⟩ := hg A h rc hrc
    obtain ⟨k1, -, k3, -⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g1) g2
    exact ⟨k1, k3⟩
  · exact ⟨wdOf h hw ι r, isWDOf_wdOf hw ι hRc, fun g => (H.away w hw A h rc hrc (σ w) (hσ w)).tor g.1 g.2⟩
  · obtain ⟨-, k2, -, k4⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g.1) g.2
    exact ⟨k2, k4.tor g.1 g.2⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HeckeGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
private theorem semisimple_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) H
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group
private theorem attC_conj {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {π : CuspSub F n} (h : RepIso r r')
    (H : AttC ι r π) : AttC ι r' π :=
  ⟨semisimple_conj h H.1, H.2.mono fun _ ⟨B, hB, hE⟩ => ⟨B, hB, hE.of_iso h⟩⟩
private theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    tw (tw r μ) μ⁻¹ = r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]
private theorem algPos_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos χ⁻¹ (-a) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
private theorem regAlg_tw {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {a : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ a) : (CG.mk (P.twist κ)).IsRegAlg := by
  have halg : κ.IsAlg a := fun k => hκ k fun φ => absurd
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  replace h := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 h
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 a halg τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + a τ, by push_cast; ring⟩
theorem aIsoTwOf_alt : _root_.UpperTheory.V.Z.Win.AIsoTwOfAlt := by
  intro FL WT _ F Ω _ _ _ _ _ _ l _ ι n r hW
  refine ⟨fun r' hi => ⟨fun v hv h => ?_, fun π hreg ha => ?_⟩, fun μ hμ => ?_⟩
  · exact (((FL F Ω l n r).1 r' hi).2.2 v).2 (hW.1 v hv ((((FL F Ω l n r').1 r hi.symm').2.2 v).1 h))
  · obtain ⟨t, ht⟩ := hW.2 π hreg (attC_conj hi.symm' ha)
    exact ⟨t, fun v hv => ht v (hv.imp id (((FL F Ω l n r').1 r hi.symm').2.2 v).2)⟩
  · obtain ⟨χ, -, art, a, hart, hpos, hL⟩ := hμ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : tw r μ = r := MonoidHom.ext fun s => Units.ext (by ext i; exact i.elim0)
      rw [e]
      exact hW
    have hv : ∀ v, (Unl1 (tw r μ) v → Unl1 r v) ∧ (PotUnl r v → PotUnl (tw r μ) v) ∧ (PotUnl (tw r μ) v → PotUnl r v) := fun v =>
      have h := ((FL F Ω l n r).2.1 μ).2.2 v
      ⟨h.1.2, h.2.1, h.2.2⟩
    refine ⟨fun v hl h => (hv v).2.1 (hW.1 v hl ((hv v).1 h)), fun π' hreg ha => ?_⟩
    have hatt : AttC ι r (π'.twist χ⁻¹) := by
      have h := UpperTheory.V.Af.Cq.attTwist F Ω l ι n (tw r μ) π' ha art χ⁻¹ (-a) μ⁻¹ hart hL.inv
      rwa [tw_tw_inv] at h
    obtain ⟨t, ht⟩ := hW.2 _ (regAlg_tw hreg (algPos_inv hpos)) hatt
    obtain ⟨b, hb⟩ := WT F χ
    refine ⟨t + b, fun v h => ?_⟩
    have h1 := hb n hn _ t v (ht v (h.imp id (hv v).2.2))
    rwa [← CuspSub.twist_mul, inv_mul_cancel, CuspSub.twist_one] at h1
end UpperTheory.V.Z.Win
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypePST
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Z.J.D
theorem UpperTheory.V.Z.J.D.type_pst_of_type_v :
    _root_.UpperTheory.V.Z.J.D.TypeVAlt → _root_.UpperTheory.V.Z.J.D.PotentiallySemistableType := by
  intro hV N L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ hT
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w h
  exact hV N L Ω n hn π w A h τ hτ χ hχ rc (UpperTheory.V.Z.Win.toV' hrc) (hT rc hrc)
end
end

