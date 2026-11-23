module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinPtDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AbsMain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfLocal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPAlgType
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace AlgType
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]
end AlgType
open AlgType in
theorem algType_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') : AlgType := by
  intro K Ω _ _ _ _ _ l _ ι art Y a κ ha h1 h2 n j
  have H : Good art ι a κ := ⟨Y, h1, h2⟩
  have H1 : Good art ι (fun _ => 1) (cycBar K Ω l) := good_cyc ha ι
  have H0 : Good art ι 0 1 := good_one H
  have key0 : ∀ j : ℕ, Good art ι (fun _ => (j : ℤ)) (cycBar K Ω l ^ j) := by
    intro j
    induction j with
    | zero => exact good_cong H0 (funext fun _ => by simp) (pow_zero _).symm
    | succ j ih =>
      exact good_cong (good_mul ih H1) (funext fun _ => by simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring)
        (pow_succ _ _).symm
  have key : ∀ n : ℕ, Good art ι (fun e => (n : ℤ) * a e + j) (κ ^ n * cycBar K Ω l ^ j) := by
    intro n
    induction n with
    | zero => exact good_cong (key0 j) (funext fun _ => by simp) (by simp)
    | succ n ih =>
      refine good_cong (good_mul ih H) (funext fun e => ?_) ?_
      · simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring
      · rw [pow_succ]
        exact mul_right_comm _ _ _
  exact key n
end UpperTheory.V.Cu2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NormCharacterOfFrobeniusCompatibility
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
theorem UpperTheory.norm_character_of_printed_char_frobenius :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.Sol.CharFrob → UpperTheory.V.Af.Sol.NormChar := by
  intro P hC K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι η hη
  rcases hη with rfl | hN
  · exact ⟨1, rfl, Filter.Eventually.of_forall fun v => charEig_one ι v⟩
  obtain ⟨art, ha⟩ := P.litN.aut.art K Ω
  have hm : 0 < Module.finrank K M := Module.finrank_pos
  have hA : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd (χ := η) hm hN.2.1
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι hA
  have hE := hC K Ω l ι η δ ⟨hδc, art, 0, ha, hA, hL⟩
  refine ⟨δ, ?_, hE.mono fun v hv => hv.2⟩
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, CharEig ι (δ.comp (res K Ω M)) w 1 := by
    filter_upwards [hN.2.2, (tendsto_under' (K := K) (K' := M)).eventually hE] with w h1 h2
    have hf := normV_under (K := K) w
    have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ hf).2 δ _ h2.2
    rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res K Ω M s)) (f' := fun _ => 1)
    (hδc.comp (continuous_restrictScalarsHom K M Ω)) continuous_const fun v hv _ A hA σ hσ => by
      have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
      rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
      exact h
  exact MonoidHom.ext fun s => congrFun key s
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjTor
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord
section Loc
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
private theorem hasSupport_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))} (h : HasSupport π s) :
    HasSupport (contra π) (s.map Zc.dualCl) := by
  have hsm := h.isSmooth
  obtain ⟨c, x, rfl, hi, hc, e, hsub⟩ := h
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hci : ∀ a, (contra (x a).rep).IsIrreducible := fun a =>
    GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a)
  have hcu : ∀ a, IsCuspidal (contra (x a).rep) := fun a => by
    have := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a) ⟨(hc a).1, (hc a).2.2⟩).1
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA] at this
    exact (IrrGL.isCusp_of.1 this).2
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra e
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
  have H : IsCuspSupport (contra π) (fun a => (x a).1) (fun a => contra (x a).rep) := by
    refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hi) hi,
      fun a => ⟨(hc a).1, hci a, hcu a⟩, e, ?_⟩
    exact (GlobalTheory.CompanionTheory.ContraSub.main k N _ _ _ _ hsm (isSmooth_parInd e _) hsub).trans
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective)
  have e2 : (Zc.dualCl ∘ x) = fun a => IrrGL.of (contra (x a).rep) (H.2.1 a).2.2.1 (H.2.1 a).2.1 :=
    funext fun a => GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA (x a)
  rw [Multiset.map_map, e2]
  exact hasSupport_of_isCuspSupport H
private theorem hasSupport_of_invT (c : k ≃+* k') (hc : Continuous c) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) V) (τ : Representation ℂ (GL (Fin N) k') W)
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g v, τ (GlobalTheory.LFun.ConjPlace.invT c N g) (T v) = T (σ g v))
    {s : Multiset (IrrGL (k := k))} (h : HasSupport σ s) :
    HasSupport τ ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL c (GlobalTheory.LocalFieldIso.continuous_symm c hc))) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm c hc
  obtain ⟨E⟩ := GlobalTheory.GelfandKazhdan.equiv_contra k N V σ (hA k N V σ h.isSmooth h.isIrreducible) h.isIrreducible
  have h1 := (hasSupport_contra h).of_equiv E.symm
  have h2 := GlobalTheory.SuppIne.hasSupport_comp c hc hc' h1
  refine h2.of_equiv (GlobalTheory.LocGL.equivOfBijective ⟨T.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩ T.bijective)
  have hg : GlobalTheory.LFun.ConjPlace.invT c N (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k
      (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) = g :=
    Units.ext (Matrix.ext fun i j => by
      rw [GlobalTheory.LFun.ConjPlace.invT_val]
      exact c.apply_symm_apply _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change T (σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) v) = τ g (T v)
  rw [← hT, hg]
private theorem dualCl_eq_of {x y : IrrGL (k := k)} (H : GlobalTheory.LocLanglands.DualCl x y) : Zc.dualCl x = y := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨n, π, π', rfl, rfl, ⟨E⟩⟩ := H
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  change IrrGL.of _ _ _ = IrrGL.of π'.ρ π'.smooth π'.irr
  exact IrrGL.of_eq_of.2 ⟨(GlobalTheory.ContraRefl.contraEquiv (equivRep π)).trans E.symm⟩
private theorem val_lt_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) < 1 ↔ valuation k x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x⁻¹
  have p1 : 0 < valuation k x := by
    rw [zero_lt_iff]; simpa using hx
  have p2 : 0 < valuation k' (i x) := by
    rw [zero_lt_iff]; simpa using hx
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ p1, inv_le_one₀ p2] at h
  rw [← not_le, ← not_le, h]
private theorem val_eq_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) = 1 ↔ valuation k x = 1 := by
  have a := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x
  have b := val_lt_one_iff i hi x
  exact ⟨fun h => le_antisymm (a.1 h.le) (not_lt.1 fun l => (b.2 l).ne h),
    fun h => le_antisymm (a.2 h.le) (not_lt.1 fun l => (b.1 l).ne h)⟩
private theorem unram_unif (i : k ≃+* k') (hi : Continuous i) (μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    μ (Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k')) = μ (ImaginaryQuadraticEtaCharacter.unif k) := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  set a : kˣ := Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k') with ha
  have hav : (a : k) = i.symm (ImaginaryQuadraticEtaCharacter.unif k' : k') := rfl
  have S := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  have S' := (ImaginaryQuadraticEtaCharacter.polFacts k').1
  have ha1 : valuation k (a : k) < 1 := by
    rw [hav]; exact (val_lt_one_iff i.symm hi' _).2 S'.1
  have hb1 : valuation k' (i (ImaginaryQuadraticEtaCharacter.unif k : k)) < 1 := (val_lt_one_iff i hi _).2 S.1
  have le1 := S.2 _ ha1
  have le2 := S'.2 _ hb1
  have pa : 0 < valuation k (a : k) := by
    rw [zero_lt_iff]; simp
  have pb : 0 < valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := by
    rw [zero_lt_iff]; simp
  have pu : 0 < valuation k' (ImaginaryQuadraticEtaCharacter.unif k' : k') := by
    rw [zero_lt_iff]; simp
  have le3 : valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) ≤ valuation k (a : k) := by
    have h1 : valuation k' (i ((ImaginaryQuadraticEtaCharacter.unif k : k) * (a : k)⁻¹)) ≤ 1 := by
      have : i (a : k) = (ImaginaryQuadraticEtaCharacter.unif k' : k') := by rw [hav]; exact i.apply_symm_apply _
      rw [map_mul, map_inv₀, this, map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ le2 zero_le'
    have h2 := (GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi _).1 h1
    rw [map_mul, map_inv₀] at h2
    simpa using (mul_inv_le_iff₀ pa).1 h2
  have he : valuation k (a : k) = valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := le_antisymm le1 le3
  have hu : μ (a * (ImaginaryQuadraticEtaCharacter.unif k)⁻¹) = 1 := hμ _ (by
    rw [Units.val_mul, map_mul, he, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ pb.ne'])
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu
private theorem isUnram_comp (i : k ≃+* k') (hi : Continuous i) {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) :
    IsUnram (μ.comp (Units.map i.symm.toRingHom.toMonoidHom)) := fun x hx =>
  hμ _ ((val_eq_one_iff i.symm (GlobalTheory.LocalFieldIso.continuous_symm i hi) _).2 hx)
private theorem unl_of_map (i : k ≃+* k') (hi : Continuous i) (q : ℕ) (s : Multiset (IrrGL (k := k)))
    (h : ImaginaryQuadraticEtaCharacter.Unl q ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i (GlobalTheory.LocalFieldIso.continuous_symm i hi)))) :
    ImaginaryQuadraticEtaCharacter.Unl q s := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  intro ξ hξ ξ' hξ' hun
  obtain ⟨h1, m1⟩ := hξ
  obtain ⟨h2, m2⟩ := hξ'
  let U : k'ˣ →* kˣ := Units.map i.symm.toRingHom.toMonoidHom
  have sm : ∀ ζ : kˣ →* ℂˣ, IsSmoothChar ζ → IsSmoothChar ((ζ⁻¹).comp U) := fun ζ hζ =>
    IsOpen.preimage (Continuous.units_map _ hi') hζ.inv
  have mem : ∀ (ζ : kˣ →* ℂˣ) (hζ : IsSmoothChar ζ), IrrGL.ofChar ζ hζ ∈ s →
      IrrGL.ofChar ((ζ⁻¹).comp U) (sm ζ hζ) ∈ (s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i hi') := fun ζ hζ hm =>
    Multiset.mem_map.2 ⟨IrrGL.ofChar ζ⁻¹ hζ.inv, Multiset.mem_map.2 ⟨_, hm,
      dualCl_eq_of (GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ hζ hζ.inv rfl)⟩,
      GlobalTheory.DegOneChar.trGL_ofChar i hi' _ _ _⟩
  have e : ((ξ'⁻¹).comp U) * ((ξ⁻¹).comp U)⁻¹ = (ξ * ξ'⁻¹).comp U :=
    MonoidHom.ext fun x => by simp [mul_comm]
  have := h ((ξ'⁻¹).comp U) ⟨sm _ h2, mem _ _ m2⟩ ((ξ⁻¹).comp U) ⟨sm _ h1, mem _ _ m1⟩
    (by rw [e]; exact isUnram_comp i hi hun)
  rw [e, MonoidHom.comp_apply] at this
  rwa [unram_unif i hi _ hun] at this
end Loc
theorem conj_torsion_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → ConjTor := by
  intro _ E _ _ _ n hn π hd w w' hu hT
  by_cases e : w' = w
  · subst e
    exact hT
  obtain rfl : w' = GlobalTheory.ThetaSatake.cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl ⟨hu, Or.inl e⟩
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc : Continuous (GlobalTheory.ThetaSatake.cloc w) := (conjLoc_spec _ w).1
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm _ hc
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E n π w
  have key : ∀ σ, π.IsLocComp (GlobalTheory.ThetaSatake.cw w) σ → ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v,
      τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n g) (T v) = T (σ.ρ g v) := fun σ hσ =>
    GlobalTheory.CompanionTheory.OneExDatum.exists_equiv_of_dualIsConj hd w σ τ hσ (hA _ _ _ _ σ.smooth σ.irred) hτ
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨T, hTT⟩ := key σ hσ
    obtain ⟨s, hs, h1⟩ := hT.1 τ hτ
    have hs' : HasSupport τ.ρ s := hs.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred).symm
    have h2 := hasSupport_of_invT (GlobalTheory.ThetaSatake.cloc w).symm hc' τ.ρ σ.ρ T.symm (fun g v => by
      obtain ⟨u, rfl⟩ := T.surjective v
      have := hTT (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w).symm n g) u
      have e : GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n
          (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w).symm n g) = g :=
        (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n).apply_symm_apply g
      rw [e] at this
      rw [this, T.symm_apply_apply, T.symm_apply_apply]) hs'
    refine ⟨_, h2.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), ?_⟩
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨y'', hy'', rfl⟩ := Multiset.mem_map.1 hy'
    have := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA y'' (hs'.isCusp hy'')).2
    exact this.trans (h1 _ hy'')
  · rintro s ⟨σ, hσ, hs⟩
    obtain ⟨T, hTT⟩ := key σ hσ
    have h2 := hasSupport_of_invT (GlobalTheory.ThetaSatake.cloc w) hc σ.ρ τ.ρ T hTT hs
    have h3 := hT.2 _ ⟨τ, hτ, h2⟩
    rw [GlobalTheory.ThetaSatake.absNorm_cw]
    exact unl_of_map (GlobalTheory.ThetaSatake.cloc w) hc _ _ h3
end UpperTheory.V.Z.Ord
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolGL2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host
namespace UpperTheory.V.Sd.Wc
private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp
private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)
end UpperTheory.V.Sd.Wc
open UpperTheory.V UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.polGL2_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrConc
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
end
def SeedPtOfAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka), IsKa σ M ι n ka → ∀ (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), ¬ l ∣ orderOf χ' →
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s).val.1‖ < 1) →
    ∀ (m : ℕ), 2 ≤ m → ∀ r : G L Ω →* GL (Fin n) (Qbar l),
    _root_.UpperTheory.V.Sd.IsSeedAlt ι σ (fun i => ((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω))
      (fun i => (χ' ^ Fr.w n i).comp (galEmb ℚ L Ω)) (fun i => m * Fr.w n i) ka r →
    ∀ J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J
end UpperTheory.V.Pr
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrLinkedEnd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
theorem modularity_linked_ends (hMod : _root_.UpperTheory.V.W.ModUAlt) (hLam : W.LamEx)
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
    {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (hL : W.Large L c₁)
    (hs : ∀ J, R.B₀.PointTheoremBaseObject ι J → R.T.IdealSpecializationPoint J) :
    ∃ J : Ideal R.T.B.B, R.T.ModIn J ∧ R.B₀.arithmeticPointClassicalityDense ι J := by
  obtain ⟨hd, hμ⟩ := degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  obtain ⟨Λ, hΛ⟩ := hLam l L Ω R.s R.V c₁ n R.r
  have hn : 1 ≤ n := by rcases R.n23 with h | h <;> omega
  obtain ⟨J, hJ⟩ := hMod l L Ω R.s R.V R.hV hμ c₁ hL n hn R.r R.B₀ Λ ι
  refine ⟨J, ⟨⟨Λ, hJ.ring.fin⟩, ?_, fun g hg => (hJ.ring.unr0 R.v0 g hg).1,
    n4Of Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f n ka R, hJ.p1, hJ.p3, hs J hJ.pt⟩, hJ.end2⟩
  intro Z hZ
  haveI : IsDiscreteValuationRing c₁.O := c₁.dvr
  have := dimOf c₁.O Λ.Λ R.B₀.B (Λ.toPair R.B₀.u : Λ.Λ →+* R.B₀.B) J _ hΛ hJ.ring.fin hJ.ring.tf Z hZ
  rw [← hd] at this
  exact this
end UpperTheory.V.Pr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakePolarizationOfCuspidalTransfer
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
private theorem hasSat_invT {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π π' : TR.CuspSub F a}
    (h : IsInvTOf π π') {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    π'.HasSat w (B.map (·⁻¹)) := by
  obtain ⟨e, he, -⟩ := h
  refine InvT.hasSatGL_invT e (fun g x => ?_) hB
  rw [TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]
private theorem isTwistOf_twist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (χ : HChar F) : IsTwistOf π χ (π.twist χ) := by
  refine ⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  · have e : u = TR.expU z := Units.ext (funext hu)
    rw [e]
    exact TR.chiInf_expU χ z
  all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]
theorem UpperTheory.satake_polarization_real_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.Sol.PolSatR := by
  intro H F _ _ _ n hn π ψ h
  obtain ⟨π₁, h₁, -⟩ := UpperTheory.exists_contragredient_cuspSub F n π
  obtain ⟨B, hl, hr', hf, hc, hX⟩ := H.gkR F n π
  refine isSelfDualBy_of_iso B hl hr' hf hc hX h₁ (isTwistOf_twist π₁ ψ) (H.smoR F n hn _ _ ?_)
  filter_upwards [h] with w ⟨hu, S, hS, hE⟩
  refine ⟨S, hS, ?_⟩
  have e : (S.map (·⁻¹)).map (· * ψ.val w) = S := by
    rw [hE, Multiset.map_map]
    simp
  exact e ▸ (hasSat_invT h₁ hS).twist hu
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocFixed
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Af.locFixed_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Af.LocFixedAlt
end
end

