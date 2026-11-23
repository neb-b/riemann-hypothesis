module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem orth_translate_lowV {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ) (hκ : κ ∈ lowV ε i)
    (h : ∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) (k : KG ε) :
    ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  cases i with
  | zero =>
    have h0 : κ = 0 := by simpa [lowV] using hκ
    subst h0
    simp
  | succ i =>
    have hq : (fun x : KG ε => star (κ (x⁻¹ * k))) ∈ lowV ε (i + 1) := by
      have h1 : κ ∈ polyV ε i := hκ
      have h2 := mul_right_mem k h1
      have h3 := inv_mem h2
      exact star_mem h3
    have h4 := h _ hq
    have h5 : ∫ x, star (star (κ (x⁻¹ * k)) * p x) ∂(muK ε) = 0 := by
      have := congrArg star h4
      rw [star_zero] at this
      rw [← this]
      exact integral_conj
    rw [← h5]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [star_mul', star_star]
    ring

end GlobalTheory.KFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PageOKRun
section
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.RunJoin.Inh
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin

theorem nums {A k b s PP TO rd r d q fm : ℝ} (h : Bs A k b s PP TO rd) (hr0 : 0 ≤ r) (hr : r ≤ A) (hd0 : 0 ≤ d)
    (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) (hf0 : 0 ≤ fm) (hf : fm ≤ k ^ 4) :
    (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ q ∧ TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 ≤ q ∧
      2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ q := by
  have hs : (10 : ℝ) ^ 100 ≤ s := h.sb_ge
  have hs1 : (40000 : ℝ) ≤ s := le_trans (by norm_num) hs
  have hk : (1 : ℝ) ≤ k := by linarith [h.k8]
  have hR : rd ^ 7 ≤ s := h.rd_pow_le (by norm_num)
  have hR0 : 0 ≤ rd ^ 7 := by have := h.rd1; positivity
  have hP0 : 0 ≤ PP := le_trans (by positivity) h.PP_ge
  have hP := h.PP_le_sb
  have hP3 := h.param_cube_le_bound
  have hTP := h.hTP
  have hT0 : 0 ≤ TO := by linarith [h.one_le_order_alt]
  have hb : b = s ^ 2 := by rw [← h.sb_sq]; ring
  have hd' : d ≤ 4 * k ^ 2 * s ^ 2 := by
    have := h.Ak
    rw [hb] at hd
    have : A * s ^ 2 ≤ 2 * k ^ 2 * s ^ 2 := by gcongr
    linarith
  have hq' : k ^ 8 * s ^ 16 ≤ q := by rw [hb] at hq; calc k ^ 8 * s ^ 16 = (k * s ^ 2) ^ 8 := by ring
    _ ≤ q := hq
  have hr' : r ≤ 2 * k ^ 2 := hr.trans h.Ak
  have key : ∀ (a c : ℕ) (C : ℝ), a ≤ 8 → c ≤ 15 → 0 ≤ C → C ≤ 40000 → C * (k ^ a * s ^ c) ≤ q := by
    intro a c C ha hc hC0 hC
    have e1 : k ^ a ≤ k ^ 8 := pow_le_pow_right₀ hk ha
    have e2 : s ^ c ≤ s ^ 15 := pow_le_pow_right₀ (by linarith) hc
    calc C * (k ^ a * s ^ c) ≤ s * (k ^ 8 * s ^ 15) := by gcongr; linarith
      _ = k ^ 8 * s ^ 16 := by ring
      _ ≤ q := hq'
  refine ⟨?_, ?_, ?_⟩
  · calc (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ s ^ 4 * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 16 * (k ^ 4 * s ^ 9) := by ring
      _ ≤ q := key 4 9 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 = (TO * PP) * (1250 * r) * rd ^ 7 * d ^ 2 := by ring
      _ ≤ s * (1250 * (2 * k ^ 2)) * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 40000 * (k ^ 6 * s ^ 6) := by ring
      _ ≤ q := key 6 6 40000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc 2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ 2 * (k ^ 4 * s ^ 2 * (s * s * (4 * k ^ 2 * s ^ 2) ^ 2)) := by gcongr
      _ = 32 * (k ^ 8 * s ^ 8) := by ring
      _ ≤ q := key 8 8 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem eRR7 : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
  unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7

end GlobalTheory.RunJoin.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PolyTranslationL2Bound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem sq_intervalIntegral_unit_le (h : ℝ → ℝ) (hc : Continuous h) :
    (∫ s in (0:ℝ)..1, h s) ^ 2 ≤ ∫ s in (0:ℝ)..1, h s ^ 2 := by
  set c := ∫ s in (0:ℝ)..1, h s with hcdef
  have hnn : 0 ≤ ∫ s in (0:ℝ)..1, (h s - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
  have hexp : ∫ s in (0:ℝ)..1, (h s - c) ^ 2 = (∫ s in (0:ℝ)..1, h s ^ 2) - 2 * c * c + c ^ 2 := by
    have e1 : (fun s => (h s - c) ^ 2) = fun s => (h s ^ 2 - (2 * c) * h s) + c ^ 2 := by
      funext s; ring
    rw [e1, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    · simp
      exact Or.inl rfl
    · exact (hc.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hc).intervalIntegrable _ _
    · exact ((hc.pow 2).sub (continuous_const.mul hc)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  nlinarith

theorem norm_sub_expK_sq_le : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ Y : Mx n, inK ε Y → ∫ x, ‖φ x - φ (x * expK ε Y 1)‖ ^ 2 ∂(muK ε) ≤ ∫ x, ‖rder ε [Y] φ x‖ ^ 2 ∂(muK ε) := by
  intro n ε d φ hφ Y hY
  obtain ⟨hRmem, hRder⟩ := rder_mem_and_hasDerivAt ε d φ hφ Y hY
  set R := rder ε [Y] φ with hRdef
  have hRc : Continuous R := continuous_of_mem hRmem
  have hφc : Continuous φ := continuous_of_mem hφ
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hEG := group_exponential_facts n ε Y hY.1
  have hEK := hEG.2.2.2 hY
  let e : ℝ → KG ε := fun t => expK ε Y t
  have he_add : ∀ s t, e (s + t) = e s * e t := fun s t => by
    apply Subtype.ext
    show ((expK ε Y (s + t) : KG ε) : UJ ε) = (expK ε Y s : UJ ε) * (expK ε Y t : UJ ε)
    rw [hEK.1, hEK.1, hEK.1]
    exact hEG.2.1 s t
  have he0 : e 0 = 1 := by
    apply Subtype.ext
    show ((expK ε Y 0 : KG ε) : UJ ε) = 1
    rw [hEK.1]; exact hEG.1
  have he_cont : Continuous e := hEK.2
  have hder' : ∀ k s, HasDerivAt (fun t => φ (k * e t)) (R (k * e s)) s := by
    intro k s
    have h1 := hRder (k * e s)
    have h2 : HasDerivAt (fun t => φ (k * e s * expK ε Y (t - s))) (R (k * e s)) s :=
      HasDerivAt.comp_sub_const (f := fun t => φ (k * e s * expK ε Y t)) s s (by rw [sub_self]; exact h1)
    have hfun : (fun t => φ (k * e s * expK ε Y (t - s))) = fun t => φ (k * e t) := by
      funext t
      show φ (k * e s * e (t - s)) = φ (k * e t)
      rw [mul_assoc, ← he_add, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  have hgc : ∀ k, Continuous (fun s => R (k * e s)) := fun k =>
    hRc.comp (continuous_const.mul he_cont)
  have hftc : ∀ k, ∫ s in (0:ℝ)..1, R (k * e s) = φ (k * e 1) - φ k := by
    intro k
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder' k s)
      ((hgc k).intervalIntegrable 0 1), he0, mul_one]
  have hpt : ∀ k, ‖φ k - φ (k * e 1)‖ ^ 2 ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ ^ 2 := by
    intro k
    have h1 : ‖φ k - φ (k * e 1)‖ ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ := by
      rw [norm_sub_rev, ← hftc k]
      exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    have h2 := sq_intervalIntegral_unit_le (fun s => ‖R (k * e s)‖) ((hgc k).norm)
    calc ‖φ k - φ (k * e 1)‖ ^ 2 ≤ (∫ s in (0:ℝ)..1, ‖R (k * e s)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hRsc : Continuous (fun x => ‖R x‖ ^ 2) := hRc.norm.pow 2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hRsc.continuousOn
  have hcont2 : Continuous (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2) :=
    hRsc.comp (continuous_fst.mul (he_cont.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2)
      ((muK ε).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [isFiniteMeasure_restrict]; simp
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    haveI : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (KG ε × ℝ) := inferInstance
    exact Integrable.of_bound hcont2.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _ (Set.mem_univ _))
  have hswap := integral_integral_swap hI
  have hrhs : ∫ x, (∫ s in (0:ℝ)..1, ‖R (x * e s)‖ ^ 2) ∂(muK ε) = ∫ x, ‖R x‖ ^ 2 ∂(muK ε) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    rw [hswap]
    simp_rw [integral_mul_right_eq_self (μ := muK ε) (fun x => ‖R x‖ ^ 2)]
    rw [setIntegral_const]
    simp
  rw [← hrhs]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x => by positivity
  · have := hI.integral_prod_left
    simp only [Function.uncurry_apply_pair] at this
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [intervalIntegral.integral_of_le zero_le_one]
  · exact Filter.Eventually.of_forall fun x => hpt x

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonSectionsOfNoLeadingTerm
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin.NoPoint

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem subsingleton_sections_of_no_leadingTerm (G : GlobalFamilyData X ka wL wF) (hd : G.del = 0) (la : HeightOneSpectrum (𝓞 B.KO))
    (hB : InBasis G la) : Subsingleton (SectionSheafQuotient X la G.w wF) := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have h := hB.2
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact (Submodule.subsingleton_iff (Kp X la G.N)).1 (subsingleton_of_bot_eq_top h)

theorem heights_of_del_zero (G : GlobalFamilyData X ka wL wF) (Q : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have hI : ∀ la, (Q la).Ila = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    unfold LocalPointData.Ila
    exact Module.length_eq_zero
  have hN : ∀ la, (Q la).Net = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    haveI : Subsingleton (OsK X la G.w) := (hC la).2.2.1.subsingleton
    haveI : IsEmpty (PtsG G la) := ⟨fun ζ => ζ.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    unfold LocalPointData.Net
    exact finsum_of_isEmpty _
  have hd' : (G.del : ℝ) = 0 := by rw [hd]; exact Nat.cast_zero
  refine ⟨fun la => by simp [hI la], by simp [hI, summable_zero], by simp [hI, hd'],
    fun _ => ⟨by simp [hN, summable_zero], by simp [hN, hd']⟩⟩

theorem inBasis_xplus (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : InBasis G la) : InBasis (gd2Xplus G E hM) la := h

theorem heights_xplus_of_del_zero (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E)
    (Q : ∀ la, LocalPointData (gd2Xplus G E hM) la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet :=
  heights_of_del_zero (gd2Xplus G E hM) Q Gc PH Prw Pet hd (fun la => inBasis_xplus G E hM la (hB la)) hC

end Abstract


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heights_no_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (Q : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la) (Gc PH Prw Pet : ℝ), G.del = 0 → (∀ la, InBasis G la) → (∀ la, (Q la).InCurve) → Heights Q Gc PH Prw Pet :=
  fun _ _ h j hj _ _ _ _ _ _ _ _ _ _ _ _ _ G Q Gc PH Prw Pet hd hB hC =>
    heights_xplus_of_del_zero G (extAll h j hj) (intAtExt_extAll h j hj) Q Gc PH Prw Pet hd hB hC

end GlobalTheory.RunJoin.NoPoint
end

