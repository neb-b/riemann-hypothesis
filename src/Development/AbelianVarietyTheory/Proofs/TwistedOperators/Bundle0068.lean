module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0062
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0063
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatricesStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.CompactOfMatBounded := by
  first | exact @GlobalTheory.RegSS.CptQuot.compactOfMatBounded | exact GlobalTheory.RegSS.CptQuot.compactOfMatBounded | (intros; apply GlobalTheory.RegSS.CptQuot.compactOfMatBounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotentStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent : GlobalTheory.RegSS.IdempotentDet → GlobalTheory.RegSS.NotCompactOfIdempotent := by
  first | exact @GlobalTheory.RegSS.notCompactOfIdempotent_of | exact GlobalTheory.RegSS.notCompactOfIdempotent_of | (intros; apply GlobalTheory.RegSS.notCompactOfIdempotent_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactorsStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unit_translate_bounded_of_factors : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.ProductUnitBounded := by
  first | exact @GlobalTheory.RegSS.productUnitBounded | exact GlobalTheory.RegSS.productUnitBounded | (intros; apply GlobalTheory.RegSS.productUnitBounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBoundStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_splitRank_upper_bound : GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SeparatingPoints → GlobalTheory.RegSS.SplitRankUpper := by
  first | exact @GlobalTheory.RegSS.SplitRankBound.splitRankUpper | exact GlobalTheory.RegSS.SplitRankBound.splitRankUpper | (intros; apply GlobalTheory.RegSS.SplitRankBound.splitRankUpper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtensionEmbeddingMixedSymmOfIsComplex
section
noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)

namespace GlobalTheory.HeckeOne

theorem exists_eq_circleExp_mul (f : ℝ → Circle) (hf : Continuous f) (hadd : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ x, f x = Circle.exp (a * x) := by
  have h0 : f 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts ⟨f, hf⟩ 0 0
    (by simp [h0])
  have hF' : ∀ x, Circle.exp (F x) = f x := fun x => congrFun hF x
  have hFadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y : ℝ => F (x + y) - F x - F y := by fun_prop
    have := Circle.isCoveringMap_exp.const_of_comp hc (fun y y' => by
      simp only [Circle.exp_sub, hF', hadd]
      simp) y 0
    simp only [add_zero, hF0, sub_self] at this
    linarith
  refine ⟨F 1, fun x => ?_⟩
  have := map_real_smul (AddMonoidHom.mk' F hFadd) F.continuous x 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at this
  rw [← hF', this, mul_comm]

variable (K : Type) [Field K] [NumberField K]

theorem extensionEmbedding_mixedSymm_of_isReal (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.1 ⟨v, hv⟩ :=
  congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩

theorem extensionEmbedding_mixedSymm_of_isComplex (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsComplex) :
    InfinitePlace.Completion.extensionEmbedding v
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.2 ⟨v, hv⟩ :=
  congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y => (extensionEmbedding_mixedSymm_of_isReal K y v hv).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y => (extensionEmbedding_mixedSymm_of_isComplex K y v hv).symm

def mixedIdele : (mixedSpace K)ˣ →* Ideles K :=
  Units.map ((MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.toMonoidHom)

theorem continuous_mixedIdele : Continuous (mixedIdele K) :=
  Continuous.units_map _ ((continuous_ringEquiv_mixedSpace_symm K).prodMk continuous_const)

theorem mixedIdele_mixedEmbedding (k : Kˣ) :
    mixedIdele K (Units.map (mixedEmbedding K).toMonoidHom k) = Formalism.L2.Host.infDiag k := by
  rw [GlobalTheory.CMVal.infDiag_eq]
  apply Units.ext
  apply Prod.ext
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K (k : K)) = algebraMap K _ (k : K)
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
  · rfl

def expScalar (x : ℝ) : (mixedSpace K)ˣ :=
  ⟨algebraMap ℝ _ (Real.exp x), algebraMap ℝ _ (Real.exp (-x)),
    by rw [← map_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, map_one],
    by rw [← map_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, map_one]⟩

theorem expScalar_add (x y : ℝ) : expScalar K (x + y) = expScalar K x * expScalar K y :=
  Units.ext (by
    change algebraMap ℝ (mixedSpace K) (Real.exp (x + y)) = algebraMap ℝ _ (Real.exp x) * algebraMap ℝ _ (Real.exp y)
    rw [Real.exp_add, map_mul])

theorem continuous_expScalar : Continuous (expScalar K) :=
  Units.continuous_iff.2 ⟨(continuous_algebraMap ℝ (mixedSpace K)).comp Real.continuous_exp,
    (continuous_algebraMap ℝ (mixedSpace K)).comp (Real.continuous_exp.comp continuous_neg)⟩

theorem ideleNorm_expScalar (x : ℝ) :
    ideleNorm (mixedIdele K (expScalar K x)) = Real.exp ((Module.finrank ℚ K : ℝ) * x) := by
  have h : ∀ v : InfinitePlace K, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedSpace K) (Real.exp x)) v‖ = Real.exp x := by
    intro v
    rcases v.isReal_or_isComplex with hv | hv
    · rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _),
        extensionEmbedding_mixedSymm_of_isReal]
      change ‖Real.exp x‖ = _
      exact Real.norm_of_nonneg (Real.exp_pos x).le
    · rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
        extensionEmbedding_mixedSymm_of_isComplex K _ v hv]
      change ‖((Real.exp x : ℝ) : ℂ)‖ = _
      exact Complex.norm_of_nonneg (Real.exp_pos x).le
  change (∏ v : InfinitePlace K, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedSpace K) (Real.exp x)) v‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖) = _
  simp only [h, norm_one, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, Real.exp_nat_mul]

variable {K}

theorem exists_trivial_on_expScalar (χ : HChar K) (hχ : χ.IsUnitary) :
    ∃ t : ℝ, ∀ x : ℝ, (χ * normChar K (-t)).1 (mixedIdele K (expScalar K x)) = 1 := by
  let f : ℝ → Circle := fun x => ⟨(χ.1 (mixedIdele K (expScalar K x)) : ℂ),
    mem_sphere_zero_iff_norm.2 (hχ _)⟩
  have hf : Continuous f := Continuous.subtype_mk
    (Units.continuous_val.comp (χ.2.1.comp ((continuous_mixedIdele K).comp (continuous_expScalar K)))) _
  obtain ⟨a, ha⟩ := exists_eq_circleExp_mul f hf fun x y => Circle.ext (by
    change (χ.1 (mixedIdele K (expScalar K (x + y))) : ℂ) =
      (χ.1 (mixedIdele K (expScalar K x)) : ℂ) * (χ.1 (mixedIdele K (expScalar K y)) : ℂ)
    rw [expScalar_add, map_mul, map_mul, Units.val_mul])
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨a / Module.finrank ℚ K, fun x => Units.ext ?_⟩
  change (f x : ℂ) * (((normChar K _).1 (mixedIdele K (expScalar K x)) : ℂˣ) : ℂ) = 1
  rw [normChar_apply, ideleNorm_expScalar, Real.log_exp, ha, ← Circle.coe_mul, ← Circle.exp_add]
  have : a * x + -(a / (Module.finrank ℚ K : ℝ)) * ((Module.finrank ℚ K : ℝ) * x) = 0 := by
    field_simp
    ring
  rw [this, Circle.exp_zero, Circle.coe_one]

theorem exists_normChar_smooth_homogeneous_inf : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (t : ℝ) (φ : mixedSpace K → ℂ), (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (r : ℝ) x, 0 < r → φ (r • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ k : Kˣ, φ (mixedEmbedding K (k : K)) = ((((χ * GlobalTheory.HeckeOne.normChar K (-t)).inf k : ℂˣ) : ℂ))⁻¹ := by
  intro K _ _ χ hχ
  obtain ⟨t, ht⟩ := exists_trivial_on_expScalar χ hχ
  let ξ : HChar K := χ * normChar K (-t)
  have hξ : ξ.IsUnitary := fun x => by
    change ‖((χ.1 x : ℂˣ) : ℂ) * (((normChar K (-t)).1 x : ℂˣ) : ℂ)‖ = 1
    rw [norm_mul, hχ x, isUnitary_normChar (-t) x, mul_one]
  obtain ⟨φ, hmul, hsm, hu, hiff⟩ := GlobalTheory.exists_smooth_mul_extension_of_continuous_char K ((ξ⁻¹).1.comp (mixedIdele K))
    ((ξ⁻¹).2.1.comp (continuous_mixedIdele K))
  have hu' : ∀ u : (mixedSpace K)ˣ, φ u = ((ξ.1 (mixedIdele K u) : ℂˣ) : ℂ)⁻¹ := fun u => by
    rw [hu, ← Units.val_inv_eq_inv_val]
    rfl
  refine ⟨t, φ, hmul, fun r x hr => ?_, hsm, fun x hx => ?_, fun k => ?_⟩
  · have h1 : r • x = (expScalar K (Real.log r) : mixedSpace K) * x := by
      change _ = algebraMap ℝ (mixedSpace K) (Real.exp (Real.log r)) * x
      rw [Real.exp_log hr, Algebra.smul_def]
    rw [h1, hmul, hu', ht]
    simp
  · obtain ⟨u, rfl⟩ := (hiff x).1 hx
    rw [hu', norm_inv, hξ, inv_one]
  · have := hu' (Units.map (mixedEmbedding K).toMonoidHom k)
    rw [mixedIdele_mixedEmbedding] at this
    exact this

end GlobalTheory.HeckeOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiplesStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples : GlobalTheory.RegSS.NormOnePacking → GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.FieldUnitBounded := by
  first | exact @GlobalTheory.RegSS.fieldUnitBounded_of_packing | exact GlobalTheory.RegSS.fieldUnitBounded_of_packing | (intros; apply GlobalTheory.RegSS.fieldUnitBounded_of_packing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfectStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect : GlobalTheory.RegSS.TracePerfect → GlobalTheory.RegSS.TraceClause := by
  first | exact @GlobalTheory.RegSS.traceClause_of_tracePerfect | exact GlobalTheory.RegSS.traceClause_of_tracePerfect | (intros; apply GlobalTheory.RegSS.traceClause_of_tracePerfect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentralStatement
section
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_split_subtorus_not_central : GlobalTheory.RegSS.UnitaryCommutant → GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SubtorusNotCentral := by
  first | exact @GlobalTheory.RegSS.subtorusNotCentral_of | exact GlobalTheory.RegSS.subtorusNotCentral_of | (intros; apply GlobalTheory.RegSS.subtorusNotCentral_of <;> assumption)
end

