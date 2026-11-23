module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBinaryEqAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdeal
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem unram (D : D7) : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) :=
  Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := (GlobalTheory.Mem.host_cmData D.R D.host).cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem cc_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact (Formalism.HC.HostAx.conjE_apply _ _ _).symm

end GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

open scoped Pointwise nonZeroDivisors

theorem map_mul_bar (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
      (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map
        ((Formalism.L2.Pj.hostOf D hU).bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 D.host.E)} := by
  rw [← Formalism.MainNotions.UnusedSlot33.normK_holds D cc hc, Ideal.pointwise_smul_def]
  congr 2
  refine RingHom.ext fun x => RingOfIntegers.ext ?_
  show ((Formalism.L2.Pj.barE D x : 𝓞 D.host.E) : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
  rw [Formalism.L2.Pj.barE_eq_conj]
  exact (Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul D.host.conj x).symm

theorem absNorm_ne_zero {K : Type*} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (h : I ≠ ⊥) :
    (Ideal.absNorm I : ℕ) ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)

theorem map_ne_bot (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ := by
  intro h0
  have h := map_mul_bar D hU cc hc
  rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h
  exact absNorm_ne_zero hc (by exact_mod_cast h)

theorem exists_mul_conj (D : D7) (cc c0 : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) (h0 : c0 ≠ ⊥) :
    ∃ r : D.host.E, r * D.host.conj r * ((Ideal.absNorm c0 : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) := by
  have hU := unram D
  set H := Formalism.L2.Pj.hostOf D hU
  set F := maximalRealSubfield D.host.E
  have hn0 : ((Ideal.absNorm c0 : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hn : ((Ideal.absNorm cc : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero hc
  set x : F := ((Ideal.absNorm cc : ℕ) : F) / ((Ideal.absNorm c0 : ℕ) : F) with hxdef
  have hx : x ≠ 0 := div_ne_zero hn hn0
  have hid : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x : D.host.E)) *
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0 *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [map_mul_bar D hU c0 h0, map_mul_bar D hU cc hc, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
    rw [hxdef]
    push_cast
    field_simp
  have hloc := GlobalTheory.local_norm_of_ideal_norm D.host.E H x hx
    ⟨_, _, map_ne_bot D hU c0 h0, map_ne_bot D hU cc hc, hid⟩
  have hreal : ∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ (-(H.d : F)) * b ^ 2 := by
    intro σ
    have hpos : 0 ≤ σ x := by
      rw [hxdef, map_div₀, map_natCast, map_natCast]; positivity
    exact ⟨Real.sqrt (σ x), 0, by rw [Real.sq_sqrt hpos]; ring⟩
  have hd : (-(H.d : F)) ≠ 0 := by
    have : (H.d : F) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact neg_ne_zero.2 this
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F (-(H.d : F)) x hd hx hreal hloc
  refine ⟨(a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD, ?_⟩
  have ha : D.host.conj (a : D.host.E) = a := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hb : D.host.conj (b : D.host.E) = b := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 b.2
  have hs : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.MainNotions.UnusedSlot33.PolarisationData.conj_b D
  have hs2 := D.host.sqrtMinusD_sq
  have hxE : (x : D.host.E) = (a : D.host.E) ^ 2 + (D.host.d : D.host.E) * (b : D.host.E) ^ 2 := by
    have := congrArg (fun t : F => (t : D.host.E)) hab
    push_cast at this
    rw [this]
    have hHd : ((H.d : ℕ) : D.host.E) = (D.host.d : D.host.E) := rfl
    rw [hHd]; ring
  have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hxE' : (x : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) / ((Ideal.absNorm c0 : ℕ) : D.host.E) := by
    rw [hxdef]
    push_cast
    try rfl
  rw [map_add (f := _), map_mul, ha, hb, hs]
  have key : ((a : D.host.E) + b * D.host.sqrtMinusD) * (a + b * -D.host.sqrtMinusD) = x := by
    rw [hxE]; linear_combination (-(b : D.host.E) ^ 2) * hs2
  rw [key, hxE']
  field_simp

end GlobalTheory.NormRatio

theorem GlobalTheory.NormRatio.exists_scale : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r :=
  fun D cc hcc => GlobalTheory.NormRatio.exists_mul_conj D cc D.host.ccK hcc.1 D.host.ccK_ne_bot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodicMeasurableSchwartzBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodic_measurable_schwartz_bound : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  first | exact @GlobalTheory.Cofactor.exists_cofactor | exact GlobalTheory.Cofactor.exists_cofactor | (intros; apply GlobalTheory.Cofactor.exists_cofactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schroedinger_eigenvector_compact_cocycle : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ {κ M : Type} [Fintype κ] [Fintype M] (u : M → (κ → Fv F v) × (κ → Fv F v))
      (χ : (M → v.adicCompletionIntegers F) → ℂ), Continuous χ →
      (∀ a : M → v.adicCompletionIntegers F, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1) →
      (∀ a b : M → v.adicCompletionIntegers F, χ (a + b) = χ a * χ b *
        ψ (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
          (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2)))) →
      ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧
        ∀ a : M → v.adicCompletionIntegers F, GlobalTheory.WeilM.schr ψ (∑ m, (a m : Fv F v) • u m) φ = χ a • φ := by
  first | exact @GlobalTheory.VacLoc.exists_schr_eigen | exact GlobalTheory.VacLoc.exists_schr_eigen | (intros; apply GlobalTheory.VacLoc.exists_schr_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ Y : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    At (evFin F v) Y ∧ (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    Yᵀ * incM F G.W.J + incM F G.W.J * Y.map (cA σ) = 0 ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + Y + mat k * (1 - Y)) * M = 1 ∧
      M * (1 + Y + mat k * (1 - Y)) = 1 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) := by
  first | exact @GlobalTheory.TwoFacCore.exists_skew_cayley | exact GlobalTheory.TwoFacCore.exists_skew_cayley | (intros; apply GlobalTheory.TwoFacCore.exists_skew_cayley <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardPositiveDefiniteHermitianSpaceRank
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdDefSpace

theorem exists_std_definite : ∀ (D : D7) (n : ℕ), ∃ V : HSp D, V.rank = n ∧ V.gram = 1 ∧ IsDefiniteSpace V := by
  intro D n
  refine ⟨Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n, rfl, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
    rw [Matrix.one_apply]
    by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | rfl | exact h
  · exact Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n
  · exact fun _ => Or.inl rfl

end GlobalTheory.StdDefSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWeightExponentsOfLargeGap
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.AllWt (Psi wtOf)

namespace GlobalTheory.ThetaWtGap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_nonneg_antitone (la : AllWt.Weight Dw) (m : ℤ) (ha : ∀ τ, Antitone (la τ))
    (hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → m ≤ la τ k)
    (hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → la τ k ≤ -m) :
    (∀ x, 0 ≤ (wtOf Dw la m).1 x) ∧ ∀ τ, Antitone fun i => (wtOf Dw la m).1 (τ, i) := by
  have h0 : ∀ x, 0 ≤ (wtOf Dw la m).1 x := by
    intro x
    simp only [wtOf]
    split_ifs with h hi h' hi
    · have := hb ⟨x.1, h⟩ ⟨x.2, by omega⟩ hi
      omega
    · exact le_rfl
    · have := hs ⟨_, h'⟩ ⟨Dw.p + (Dw.q - 1 - x.2), by omega⟩ (Nat.le_add_right _ _)
      omega
    · exact le_rfl
    · exact le_rfl
  refine ⟨h0, fun τ i j hij => ?_⟩
  have hi0 := h0 (τ, i)
  simp only [wtOf] at hi0 ⊢
  by_cases h : τ (H.rt : E) = H.rt0
  · simp only [dif_pos h] at hi0 ⊢
    by_cases hj : j < Dw.p
    · have hi : i < Dw.p := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨τ, h⟩ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · simpa only [dif_neg hj] using hi0
  · have h' := AllWt.conj_mem h
    simp only [dif_neg h, dif_pos h'] at hi0 ⊢
    by_cases hj : j < Dw.q
    · have hi : i < Dw.q := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨_, h'⟩ (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
        ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
      omega
    · simpa only [dif_neg hj] using hi0

theorem exists_exponents (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (m : ℕ) (la : AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (ha : ∀ τ, Antitone (la τ))
    (hg : ∀ τ, ((2 * m + 2 : ℕ) : ℤ) ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) :
    ∃ a : (E →+* ℂ) × ℕ → ℕ, Formalism.L2.Pj.Dom a (2 * m) ∧
      GlobalTheory.CovTop.laOf Dw a (2 * m) =
        la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) ∧
      ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p →
        (((2 * m) / 2 : ℕ) : ℤ) < GlobalTheory.CovTop.laOf Dw a (2 * m) τ k := by
  set lb : AllWt.Weight Dw := la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) with hlb
  have e : ∀ τ k, lb τ k = la τ k + (1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) := fun _ _ => rfl
  have hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (m : ℤ) < lb τ k := by
    intro τ k hk
    have := ha τ (show k ≤ (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) from Fin.le_def.2 (by simp only; omega))
    rw [e]; omega
  have hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → lb τ k ≤ -(m : ℤ) := by
    intro τ k hk
    have hk2 := k.2
    have hlt : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
    have h1 := hg τ
    rw [GlobalTheory.CompHS.gap, dif_pos hlt] at h1
    have h2 := ha τ (show (⟨Dw.p - 1 + 1, hlt⟩ : Fin (Dw.p + Dw.q)) ≤ k from Fin.le_def.2 (by simp only; omega))
    rw [e]; push_cast at h1; omega
  have hanti : ∀ τ, Antitone (lb τ) := fun τ i j hij => by
    have := ha τ hij
    rw [e, e]; omega
  obtain ⟨h0, h1⟩ := wtOf_nonneg_antitone lb m hanti (fun τ k hk => (hb τ k hk).le) hs
  have hm : 2 * m / 2 = m := by omega
  have hla : GlobalTheory.CovTop.laOf Dw (fun x => ((wtOf Dw lb m).1 x).toNat) (2 * m) = lb := by
    rw [GlobalTheory.CovTop.laOf, hm]
    simp only [Int.toNat_of_nonneg (h0 _)]
    exact AllWt.weightOf_wtOf lb m
  refine ⟨fun x => ((wtOf Dw lb m).1 x).toNat, ⟨fun τ i j hij => Int.toNat_le_toNat (h1 τ hij), even_two_mul m⟩, hla, ?_⟩
  intro τ k hk
  rw [hla, hm]
  exact hb τ k hk

end GlobalTheory.ThetaWtGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVolumeOneMeasureDefiniteOpenCompact
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteLevelMeasure

theorem exists_isMeasDef_openCompact : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsDefiniteSpace V → IsOpenCompactLevel V K →
  ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 := by
  intro D V K hV hK
  have hd : ∀ ρ : D.what₂.Tau, (V.sig (tauE D ρ)).1 = 0 ∨ (V.sig (tauE D ρ)).2 = 0 := by
    intro ρ
    rcases hV.2 (tauE D ρ) with h | h <;> rw [h] <;> simp
  choose ν hν hg using fun ρ => GlobalTheory.Mem.DefiniteMeasure.exists_probHaar _ _ (hd ρ)
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV.1 K hK.1 hK.2
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν (fun ρ => (hg ρ _).2 rfl)
    (fun ρ m h => (hg ρ m).1 h)
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.DefiniteLevelMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpInt
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

theorem symm_mem_latR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {g : GlobalTheory.CuspRep.GA E k} (hg : g ∈ GlobalTheory.UnitaryBC.latticeGL E k) :
    (glTens F E k).symm g ∈ latR F E k := by
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
  rw [map_mul, map_zpow]
  refine mul_mem (Subgroup.mem_sup_left ⟨γ, ?_⟩) (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) n)
  apply (glTens F E k).injective
  rw [glTens_bc, ContinuousMulEquiv.apply_symm_apply]

def latEquiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) : GlobalTheory.UnitaryBC.latticeGL E k ≃ latR F E k where
  toFun g := ⟨(glTens F E k).symm g, symm_mem_latR g.2⟩
  invFun x := ⟨glTens F E k x, latR_le k x.2⟩
  left_inv g := Subtype.ext ((glTens F E k).apply_symm_apply _)
  right_inv x := Subtype.ext ((glTens F E k).symm_apply_apply _)

theorem finvol_tens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))]
    [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E)))
    (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (latR F E k) D ν → ν D ≠ ⊤ := by
  intro F E _ _ _ _ _ _ k _ _ ν D hν hD
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let f := (glTens F E k).toHomeomorph.toMeasurableEquiv
  let μ : Measure (GlobalTheory.CuspRep.GA E k) := ν.map f
  haveI : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (glTens F E k)
  have hq : Measure.QuasiMeasurePreserving f.symm μ ν :=
    (MeasurePreserving.mk f.symm.measurable (f.map_symm_map)).quasiMeasurePreserving
  have hD' : IsFundamentalDomain (GlobalTheory.UnitaryBC.latticeGL E k) (f '' D) μ :=
    hD.image_of_equiv f.toEquiv hq (latEquiv F E k) fun g x => by
      change glTens F E k ((glTens F E k).symm g * x) = g * glTens F E k x
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have h1 : ν D = μ (f '' D) := by
    rw [f.map_apply, f.preimage_image]
  rw [h1, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hD']
  haveI := (GlobalTheory.CovolGL.finvol E k μ).1
  exact measure_ne_top _ _

end GlobalTheory.GLOneVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  first | exact @GlobalTheory.FrameTransport.frConj_mem_UA | exact GlobalTheory.FrameTransport.frConj_mem_UA | (intros; apply GlobalTheory.FrameTransport.frConj_mem_UA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLatticStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  first | exact @GlobalTheory.FrameColSmul.mulVec_mem | exact GlobalTheory.FrameColSmul.mulVec_mem | (intros; apply GlobalTheory.FrameColSmul.mulVec_mem <;> assumption)
end

