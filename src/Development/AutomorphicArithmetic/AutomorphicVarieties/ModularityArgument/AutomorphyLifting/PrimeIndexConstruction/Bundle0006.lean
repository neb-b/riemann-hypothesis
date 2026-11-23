module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSquareMixedExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0065
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0071
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0072
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0073
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.IndGlobOfKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0070

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContDelta
section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth UpperTheory.V

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourTensorSourceAtPrime

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous

private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F

private theorem cont_delta (d : UpperTheory.V.Cu.Dat Ω l) : Continuous (toB d.δ) := by
  have h : Continuous fun g => ((toB d.δ g : (Qbar l)ˣ) : Qbar l) := ((UpperTheory.integrality_of_norm_coefficients l).2 d.c _ _).1 d.tw.cont
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun g => (toB d.δ g).ne_zero

end UpperTheory.V.Cu.RankFourTensorSourceAtPrime
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ExistsPrimeIndex
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open UpperTheory.V.Z.Gam UpperTheory.V.Z.Win UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Z.Win.Birth GroundTheory.Global.SemiLocal UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth.UnramifiedPlaceWindow

private theorem window_pow {N M f : ℕ} (hf : 0 < f) (hM : M = N ^ f) {a b x y : ℝ} (hx : 0 ≤ x) (hy : y = x ^ f)
    (h : (N : ℝ) ^ a < x ∧ x < (N : ℝ) ^ b) : (M : ℝ) ^ a < y ∧ y < (M : ℝ) ^ b := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key : ∀ c : ℝ, (M : ℝ) ^ c = ((N : ℝ) ^ c) ^ f := fun c => by
    rw [hM, Nat.cast_pow, ← Real.rpow_natCast (N : ℝ) f, ← Real.rpow_mul hN, mul_comm, Real.rpow_mul hN,
      Real.rpow_natCast]
  rw [key, key, hy]
  exact ⟨pow_lt_pow_left₀ h.1 (Real.rpow_nonneg hN _) hf.ne', pow_lt_pow_left₀ h.2 hx hf.ne'⟩

section Norm

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem nm_val {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver M v)
    (i : v.adicCompletion K ≃+* w.1.adicCompletion M) (hi : IsCompl i) (x : (w.1.adicCompletion M)ˣ) :
    ((nm w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = i.symm x := by
  haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2
  haveI : FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion M) := GroundTheory.Global.finite_adicCompletion v w.1
  have hmap : ∀ a, algebraMap (v.adicCompletion K) (w.1.adicCompletion M) a = i a := by
    intro a
    change completionMap v w.1 a = i a
    refine (HeightOneSpectrum.denseRange_algebraMap K v).induction_on a
      (isClosed_eq (continuous_completionMap v w.1) hi.1) fun k => ?_
    rw [completionMap_algebraMap, hi.2, IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M)]
  have hb : Function.Bijective (algebraMap (v.adicCompletion K) (w.1.adicCompletion M)) := by
    have : (algebraMap (v.adicCompletion K) (w.1.adicCompletion M) : _ → _) = i := funext hmap
    rw [this]
    exact i.bijective
  have h1 : Module.finrank (v.adicCompletion K) (w.1.adicCompletion M) = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId (v.adicCompletion K) (w.1.adicCompletion M)) hb).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  obtain ⟨a, ha⟩ := i.surjective (x : w.1.adicCompletion M)
  change Algebra.norm (v.adicCompletion K) (x : w.1.adicCompletion M) = i.symm x
  rw [← ha, ← hmap, Algebra.norm_algebraMap, h1, pow_one, hmap, i.symm_apply_apply]

private noncomputable def oneEquiv (h1 : Module.finrank K M = 1) : K ≃+* M :=
  RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)

private theorem over_under (h1 : Module.finrank K M = 1) (w : HeightOneSpectrum (𝓞 M)) :
    GlobalTheory.IsoPull.Over (oneEquiv h1) (w.under (𝓞 K)) w := fun x => by
  have e : algebraMap (𝓞 K) (𝓞 M) x = RingOfIntegers.mapRingEquiv (oneEquiv h1) x := RingOfIntegers.ext rfl
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, e]

private theorem normV_under (h1 : Module.finrank K M = 1) (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) := by
  rw [GlobalTheory.DegOneLift.normV_eq_absNorm, GlobalTheory.DegOneLift.normV_eq_absNorm]
  exact GlobalTheory.IsoPull.qV_eq (over_under h1 w)

variable [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex M]

private theorem win_one (h1 : Module.finrank K M = 1) {n : ℕ} (hn : 1 ≤ n) (π : CuspSub K n) (P : CuspSub M n)
    (hL : GlobalTheory.GalCut.IsLift π P) (t : ℝ) (w : HeightOneSpectrum (𝓞 M))
    (hW : WinAt π t (w.under (𝓞 K))) : WinAt P t w := by
  have hO := over_under h1 w
  let i : (w.under (𝓞 K)).adicCompletion K ≃+* w.adicCompletion M := GlobalTheory.IsoPull.locEquiv hO
  have hi : IsCompl i := ⟨GlobalTheory.IsoPull.continuous_cLoc hO, fun x => GlobalTheory.IsoPull.cLoc_algebraMap hO x⟩
  have hi' : Continuous i.symm := GlobalTheory.LocalFieldIso.continuous_symm i hi.1
  obtain ⟨s0, hs0⟩ := (suppFacts K n hn π (w.under (𝓞 K))).1
  obtain ⟨σ, hσ, hS⟩ := id hs0
  obtain ⟨s', σ', hσ', -⟩ := (suppFacts M n hn P w).1
  obtain ⟨T, hT⟩ := hL.loc _ w i hi.1 hi.2 σ σ' hσ hσ'
  have hg : ∀ g : GL (Fin n) (w.adicCompletion M),
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (σ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) σ'.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨T.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change T (σ.ρ (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) x) = σ'.ρ g (T x)
      rw [hT, hg]⟩ T.bijective
  have hP : SuppAt P w (s0.map (GlobalTheory.SuppIne.trGL i hi')) :=
    ⟨σ', hσ', (GlobalTheory.SuppIne.hasSupport_comp i hi.1 hi' hS).of_equiv φ⟩
  have hone : ∀ y ∈ s0, y.1 = 1 := ((suppFacts K n hn π _).2.2.1 s0 hs0).1.1 hW.1
  have hof : ∀ y ∈ s0, ∃ (χ : ((w.under (𝓞 K)).adicCompletion K)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
      (h' : IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom))), y = IrrGL.ofChar χ hχ ∧
        GlobalTheory.SuppIne.trGL i hi' y = IrrGL.ofChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) h' := fun y hy => by
    obtain ⟨χ, hχ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (hone y hy)
    have h' : IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) :=
      IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') hχ
    exact ⟨χ, hχ, h', rfl, GlobalTheory.DegOneChar.trGL_ofChar i hi' χ hχ h'⟩
  refine ⟨((suppFacts M n hn P w).2.2.1 _ hP).1.2 fun y hy => ?_, fun s hs ξ hξ => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨χ, hχ, h', -, e⟩ := hof z hz
    rw [e]
    rfl
  · obtain rfl := (suppFacts M n hn P w).2.1 _ _ hs hP
    obtain ⟨hξs, hm⟩ := hξ
    obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hm
    obtain ⟨χ, hχ, h', rfl, e2⟩ := hof z hz
    rw [e2, IrrGL.ofChar_inj] at hze
    subst hze
    have hb := hW.2 s0 hs0 χ ⟨hχ, hz⟩
    have hlo : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    let W : PlacesOver M (w.under (𝓞 K)) := ⟨w, hlo⟩
    have hv := normVal K M (w.under (𝓞 K)) W χ
    have hc : (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (unif (w.adicCompletion M)) =
        χ (nm W (unif (W.1.adicCompletion M))) :=
      congrArg χ (Units.ext (nm_val W i hi _).symm)
    rw [hc]
    exact window_pow hv.2.2.1 hv.2.2.2 (norm_nonneg _) (hv.2.1 hχ) hb

end Norm

section Step

variable {F E Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
  [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ}

private theorem allW_one (h1 : Module.finrank F E = 1) (hn : 2 ≤ n) (r : G F Ω →* GL (Fin n) (Qbar l))
    (ha : IsAutC ι r) (hi : IsIrr (r.comp (galEmb F E Ω))) (hA : AllW ι r) : AllW ι (r.comp (galEmb F E Ω)) := by
  obtain ⟨π, hreg, hat⟩ := ha
  obtain ⟨t, ht⟩ := hA π hreg hat
  obtain ⟨P, hP⟩ := GlobalTheory.DegOneLift.isLift F E h1 n π
  have hatt : AttC ι (r.comp (galEmb F E Ω)) P := by
    refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩
    filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hat.2] with w hw
    obtain ⟨B, hB, hF⟩ := hw
    have hq := normV_under h1 w
    have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [pow_one, hq])).1 n r _ hF
    have h4 := hP.sat w 1 B (by rw [pow_one, hq]) hB
    simp only [pow_one, Multiset.map_id'] at h3 h4
    refine ⟨B, h4, ?_⟩
    rw [hq]
    exact h3
  exact awOne E Ω l n hn ι _ P hatt ⟨t, fun w => win_one h1 (by omega) π P hP t w (ht _)⟩

private theorem allW_step [IsAlgClosure F Ω] [IsGalois F E] (hp : (Module.finrank F E).Prime) (hn : 2 ≤ n)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (ha : IsAutC ι r) (hE : IsAutC ι (r.comp (galEmb F E Ω))) (hA : AllW ι r) :
    AllW ι (r.comp (galEmb F E Ω)) := by
  obtain ⟨π, hreg, hat⟩ := ha
  obtain ⟨t, ht⟩ := hA π hreg hat
  obtain ⟨P, -, hPat⟩ := hE
  have hbc := attBC F E Ω l ι n r π P hat hPat
  refine awOne E Ω l n hn ι _ P hPat ⟨t, fun w => ?_⟩
  have hlo : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  exact (((winUpDown F E hp n hn π P hbc t (w.under (𝓞 F))).1 (ht _)) ⟨w, hlo⟩).1

end Step

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

end UpperTheory.V.Z.Win.Birth.UnramifiedPlaceWindow

open UpperTheory.V.Z.Win.Birth.UnramifiedPlaceWindow in
theorem UpperTheory.V.Z.Win.Birth.awUp :
    UpperTheory.V.Z.Win.Birth.AwUp := by
  intro hU F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r hc ha hi hA
  by_cases h1 : Module.finrank F E = 1
  · exact allW_one h1 hn r ha hi hA
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }
  haveI : IsAlgClosure F Ω := { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans F E Ω }
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
  have hiK : IsIrr (r.comp (galEmb F K Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ hi
  have haK : IsAutC ι (r.comp (galEmb F K Ω)) := hU F K Ω l ι (hdeg ▸ hp) n (by omega) r hc ha hiK
  exact ih _ hlt K rfl _ (hc.comp (resFacts F K Ω l n r).1) haK hi (allW_step (hdeg ▸ hp) hn r ha haK hA)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.SeedII
section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

section

variable {l : ℕ} [Fact l.Prime]

private theorem lt_add {a b : Qbar l} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem norm_of_cong {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have e : a = (a - b) + b := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hb]; exact h.ne), hb, max_eq_right h.le]

private theorem root_ex {a : Qbar l} (ha : ‖a - 1‖ < 1) {z : (Qbar l)ˣ} (hz : Cong z 1 ∨ Cong z (-1)) :
    ∃ α : (Qbar l)ˣ, (α : Qbar l) ^ 2 = a ∧ Cong α z := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq a two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← hx] at ha
    simp at ha
  have h1 : ∃ y : Qbar l, y ≠ 0 ∧ y ^ 2 = a ∧ ‖y - 1‖ < 1 := by
    have e : ‖x - 1‖ * ‖-x - 1‖ < 1 := by
      rw [← norm_mul, show (x - 1) * (-x - 1) = -(a - 1) by rw [← hx]; ring, norm_neg]
      exact ha
    by_cases h : ‖x - 1‖ < 1
    · exact ⟨x, hx0, hx, h⟩
    · refine ⟨-x, neg_ne_zero.2 hx0, by rw [← hx]; ring, ?_⟩
      nlinarith [norm_nonneg (-x - 1), not_lt.1 h]
  obtain ⟨y, hy0, hy, hy1⟩ := h1
  rcases hz with hz | hz
  · refine ⟨Units.mk0 y hy0, hy, ?_⟩
    have := lt_add hy1 (by rw [norm_neg]; exact hz : ‖-((z : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l))‖ < 1)
    simpa [Cong] using this
  · refine ⟨-Units.mk0 y hy0, by simpa using hy, ?_⟩
    have := lt_add hy1 hz
    rw [← norm_neg] at this
    have e : ((-Units.mk0 y hy0 : (Qbar l)ˣ) : Qbar l) - z = -(y - 1 + ((z : Qbar l) - ((-1 : (Qbar l)ˣ) : Qbar l))) := by
      rw [Units.val_neg, Units.val_neg, Units.val_mk0, Units.val_one]
      ring
    rw [Cong, e]
    exact this

end

private theorem indEx (hP : MixOfP) :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → T.Deep → ∀ ι : Qbar l ≃+* ℂ,
    ∃ (k₀ : IntermediateField ℚ Ω) (_ : NumberField k₀) (_ : IsTotallyReal k₀) (φ : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ)
      (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
      IndDat T k₀ φ ι k t r α β R δ ∧ PR ι r := by
  intro Ω _ _ _ l _ c D T hg hok h2 hd ι
  obtain ⟨k₀, _, _, φ, hyp, hrange, hidx, hemb⟩ := UpperTheory.exists_quadratic_character_of_subgroup_index_two Ω l c D T hg hok h2 hd
  have hc := UpperTheory.galois_character_residual_decomposition Ω l c D T k₀ φ hyp
  obtain ⟨k, t, r₀, dat₀, hrw⟩ := hP Ω l c D T k₀ φ ι hyp hc
  obtain ⟨u, hu⟩ : resQ T.F T.g0 * resQ T.F T.g0 ∈ (resQ k₀).range := hrange ▸ Subgroup.mul_self_mem_of_index_two hidx _
  obtain ⟨r, iso, h01, h10, rib, ns⟩ := UpperTheory.exists_ribet_lattice Ω l c D T k₀ φ ι k t r₀ hyp hc dat₀ u hu
  have dat := UpperTheory.galoisRep_properties_invariant_under_conjugation Ω l k₀ ι _ k t r₀ r dat₀ iso
  set μ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ k * up D.ξ * φ with hμ
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hdet : ∀ h, Matrix.GeneralLinearGroup.det (r h) = μ (resQ k₀ h) := fun h => by
    have e := DFunLike.congr_fun dat.det h
    have e' : φ (resQ k₀ h) = 1 := hyp.φ_in _ (hrange ▸ ⟨h, rfl⟩)
    simp only [hμ, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, e', mul_one] at e ⊢
    rw [e]
    rfl
  have ru := rib u (by rw [hu, ← map_mul]; exact hF _)
  obtain ⟨α, hα, hαc⟩ := root_ex ru.1 hc.c3
  have hmu := hc.mult k dat.dvd
  have hμ1 : ∀ g : G T.F Ω, ‖(μ (resQ T.F g) : Qbar l)‖ = 1 := fun g =>
    norm_of_cong (by rw [norm_sub_rev]; exact hmu g) (hc.unit _ _)
  have hα1 : ‖(α : Qbar l)‖ = 1 := norm_of_cong hαc (hc.unit _ _)
  obtain ⟨R, hR, hgsp⟩ := UpperTheory.symmetric_square_mixed_exists (Qbar l) _ _ (resQ k₀) (resQ T.F T.g0) α (μ (resQ T.F T.g0) / α) r μ two_ne_zero
    hemb.injective (hrange ▸ hidx) (hrange ▸ hc.out) (fun u' hu' => by
      obtain rfl : u' = u := hemb.injective (hu'.trans hu.symm)
      have e := congrArg Units.val (hdet u')
      rw [hu, map_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h10, ← hα, Units.val_mul] at e
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hα]
      · simp [h01]
      · simp [h10]
      · have := α.ne_zero
        simp only [Fin.mk_one, Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Units.val_div_eq_div_val]
        field_simp
        linear_combination e) hdet (mul_div_cancel _ _)
  have hres : Continuous (resQ T.F) := (emb ℚ T.F Ω).continuous
  obtain ⟨δ, hδc, hδ2, hδ1⟩ := UpperTheory.exists_square_root_of_character_near_one l hg.l_odd _ ((up D.th / μ).comp (resQ T.F)) ((hc.cont k).comp hres) fun g => by
    have := (μ (resQ T.F g)).ne_zero
    have e : (((up D.th / μ).comp (resQ T.F) g : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
        ((up D.th (resQ T.F g) : Qbar l) - μ (resQ T.F g)) / μ (resQ T.F g) := by
      rw [MonoidHom.comp_apply, MonoidHom.div_apply, Units.val_div_eq_div_val, Units.val_one, sub_div, div_self this]
    rw [Cong, e, norm_div, hμ1, div_one]
    exact hmu g
  haveI : FaithfulSMul k₀ Ω := (faithfulSMul_iff_algebraMap_injective k₀ Ω).2 (algebraMap k₀ Ω).injective
  haveI : Module.IsTorsionFree k₀ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  refine ⟨k₀, ‹_›, ‹_›, φ, k, t, r, α, _, R, δ, ⟨hyp, hc, dat, rib, ns, hR,
    UpperTheory.continuous_mix_family l _ _ _ _ _ _ r R hR hemb dat.cont, hgsp, hαc, ?_, hδc, fun g => ?_, hδ1⟩, prIso k₀ Ω l ι 2 r₀ r iso hrw⟩
  · have e0 := congrArg Units.val (hc.mul 0 (resQ T.F T.g0))
    have := α.ne_zero
    have e : ((μ (resQ T.F T.g0) / α : (Qbar l)ˣ) : Qbar l) - ch T 0 (resQ T.F T.g0) =
        (-((up D.th (resQ T.F T.g0) : Qbar l) - μ (resQ T.F T.g0)) +
          -(ch T 0 (resQ T.F T.g0) * ((α : Qbar l) - ch T 3 (resQ T.F T.g0)))) / α := by
      rw [← e0, Units.val_div_eq_div_val, Units.val_mul, show (0 : Fin 4).rev = 3 from rfl]
      field_simp
      ring
    rw [Cong, e, norm_div, hα1, div_one]
    refine lt_add (by rw [norm_neg]; exact hmu _) ?_
    rw [norm_neg, norm_mul, hc.unit, one_mul]
    exact hαc
  · rw [hδ2, MonoidHom.comp_apply, MonoidHom.div_apply, div_mul_cancel]
end

