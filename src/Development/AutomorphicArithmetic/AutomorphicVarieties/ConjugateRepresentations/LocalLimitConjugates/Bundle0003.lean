module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConvolutionL2Class
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.convolution_L2_class :
    UpperTheory.V.Cj.H.ConvolutionL2Class := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs F
  set f : G → ℂ := fun y => ψ y⁻¹ with hfdef
  have hfi : Integrable f μ :=
    (hψ.comp continuous_inv).integrable_of_hasCompactSupport
      (hψs.comp_homeomorph (Homeomorph.inv G))
  have hconv : cv ψ F = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F) := by
    funext x
    show ∫ y, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x) ∂μ = ∫ y, f y * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) (x * y) ∂μ
    rw [← MeasureTheory.integral_mul_left_eq_self
      (fun y => GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) x]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact mul_comm _ _
  obtain ⟨-, hae⟩ := GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR G Γ μ f hfi F
  rw [hconv]
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _).convR f
  have hdesc : GlobalTheory.AutomorphicL2Unitary.descend Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F))
      =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] ↑↑(GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f F) := by
    refine GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.2 ?_
    filter_upwards [hae] with g hg
    have hl := congrFun hinv.lift_descend g
    simp only [GlobalTheory.AutomorphicL2Unitary.lift] at hg hl
    rw [hl, hg]
  have hm : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    ⟨hinv, (MeasureTheory.Lp.memLp _).ae_eq hdesc.symm⟩
  exact ⟨hm, GlobalTheory.AutomorphicL2Unitary.l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans hae.symm)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvCount
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ENNReal in
private theorem sq_on_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℕ) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ F) 2 (μ.restrict S) ≤ N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  have hmeasF : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have key : ∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) ≤
      (N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [← lintegral_indicator hS, GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeasF.enorm.pow_const _).indicator hS),
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    refine lintegral_mono (fun q => ?_)
    have hq : ∀ γ : Γ, S.indicator (fun x => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ))
        ((γ : G) * Quotient.out q) = {γ : Γ | (γ : G) * Quotient.out q ∈ S}.indicator
          (fun _ => ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ)) γ := by
      intro γ
      have hl : GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) ((γ : G) * Quotient.out q) =
          (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q := by
        rw [GlobalTheory.AutomorphicL2Unitary.lift, GlobalTheory.AutomorphicL2Unitary.mk_mul]
        exact congrArg _ (Quotient.out_eq q)
      by_cases h : (γ : G) * Quotient.out q ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h), hl]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h)]
    rw [tsum_congr hq, ← tsum_subtype, ENNReal.tsum_set_const]
    gcongr
    have h1 := ENat.toENNReal_le.mpr (hN (Quotient.out q))
    simpa using h1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hN2 : (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp
    · calc (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (N : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by norm_num)
        _ = N := ENNReal.rpow_one _
  calc (∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = (N : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr
  all_goals first | exact Lp.aestronglyMeasurable F | exact hmeasF.restrict

theorem UpperTheory.V.Cj.H.cvCount :
    UpperTheory.V.Cj.H.CvCount := by
  open scoped Pointwise in
    intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψc
    obtain ⟨C0, hC0⟩ := hψ.bounded_above_of_compact_support hψc
    have hC : ∀ z, ‖ψ z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
    have hC' : 0 ≤ max C0 0 := le_max_right _ _
    have hMfin : μ (tsupport ψ)⁻¹ ≠ ⊤ := (hψc.isCompact.inv).measure_lt_top.ne
    refine ⟨max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ), by positivity, ?_⟩
    intro x N hN F
    have hS : MeasurableSet {y : G | ψ (y⁻¹ * x) ≠ 0} :=
      (isOpen_ne_fun (hψ.comp (continuous_inv.mul continuous_const)) continuous_const).measurableSet
    have hSK : μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ (tsupport ψ)⁻¹ := by
      calc μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ ((fun y => x⁻¹ * y) ⁻¹' (tsupport ψ)⁻¹) := by
            refine measure_mono (fun y hy => ?_)
            show (x⁻¹ * y)⁻¹ ∈ tsupport ψ
            rw [_root_.mul_inv_rev, inv_inv]
            exact subset_tsupport _ hy
        _ = μ (tsupport ψ)⁻¹ := measure_preimage_mul μ x⁻¹ _
    have hF := sq_on_le Γ μ hS N hN F
    have hmeas : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
      GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
      (hmeas.restrict (s := {y : G | ψ (y⁻¹ * x) ≠ 0}))
    rw [show (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) by norm_num,
      Measure.restrict_apply_univ] at hH
    have hE : ‖cv ψ F x‖ₑ ≤ (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (max C0 0) := by
      calc ‖cv ψ F x‖ₑ ≤ ∫⁻ y, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y * ψ (y⁻¹ * x)‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, {y : G | ψ (y⁻¹ * x) ≠ 0}.indicator
              (fun y => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ) y * ENNReal.ofReal (max C0 0) ∂μ := by
            refine lintegral_mono (fun y => ?_)
            by_cases hy : y ∈ {y : G | ψ (y⁻¹ * x) ≠ 0}
            · rw [Set.indicator_of_mem hy, enorm_mul]
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hC _)
            · have h0 : ψ (y⁻¹ * x) = 0 := not_not.mp hy
              rw [h0, mul_zero, enorm_zero]
              exact bot_le
        _ = (∫⁻ y in {y : G | ψ (y⁻¹ * x) ≠ 0}, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ ∂μ) *
              ENNReal.ofReal (max C0 0) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hS]
        _ = eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) 1 (μ.restrict {y : G | ψ (y⁻¹ * x) ≠ 0}) *
              ENNReal.ofReal (max C0 0) := by
            rw [eLpNorm_one_eq_lintegral_enorm]
            exact hmeas.restrict
        _ ≤ _ := by
            gcongr
            calc _ ≤ _ := hH
              _ ≤ _ := by gcongr
    have hRfin : (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (max C0 0) ≠ ⊤ := by
      have h1 : eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := Lp.eLpNorm_ne_top F
      have h2 : μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMfin
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) h1) h2)
        ENNReal.ofReal_ne_top
    calc ‖cv ψ F x‖ = ‖cv ψ F x‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ _ := ENNReal.toReal_mono hRfin hE
      _ = max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ) * N * ‖F‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC',
          ENNReal.toReal_rpow, ENNReal.toReal_natCast, Lp.norm_def]
        ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LatCount
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.latCount :
    UpperTheory.V.Cj.H.LatCount := by
  intro E _ _ _ a _ S hS g
  obtain ⟨A, hA⟩ := GlobalTheory.card_latticeGL_conj_le E a
  set c : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g with hc
  set f : GA E a := finGL E a (GeneralLinearGroup.map (pFin E) g) with hf
  obtain ⟨C, hC0, hC⟩ := hA ((fun s => f * s * f⁻¹) '' S) (hS.image (by fun_prop))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c))
  refine ⟨C * B ^ (2 * A), 2 * A, fun y => ?_⟩
  obtain ⟨hfin, hle⟩ := hC (c * y)
  have hg : g * infGL E a y = infGL E a (c * y) * f := by
    refine ga_ext ?_ ?_
    · simp only [map_mul, hf, pInf_infGL, pInf_finGL, mul_one, hc]
    · simp only [map_mul, hf, pFin_infGL, pFin_finGL, mul_one, one_mul]
  refine ⟨_, hle.trans ?_, ?_⟩
  · have h0 : 0 ≤ GlobalTheory.CuspRep.height (c * y) := zero_le_one.trans (one_le_height _)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hB c rfl y) _) hC0
  · rw [hfin.cast_ncard_eq]
    refine Set.encard_le_encard fun γ hγ => ⟨_, hγ, ?_⟩
    rw [hg]
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def levFnSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor (Fin d → ℂ) m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Cj.H.levLin :
    UpperTheory.V.Cj.H.LevLin := by
  intro E _ _ _ a U Ξ q
  have ap : ∀ (α β : Co Ξ q) (s t : ℂ) X, (s • α + t • β) X = s • α X + t • β X := fun _ _ _ _ _ => rfl
  refine ⟨fun α β s t hα hβ => ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, fun α β s t => ?_,
    fun α hα X i => ?_, fun T α X i => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add (f := _), map_smul, map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (Submodule.smul_mem _ _ (hβ.val X))
  · refine AlternatingMap.ext fun X => ?_
    have e : (s • dCo (smLie Ξ) α + t • dCo (smLie Ξ) β) X = s • dCo (smLie Ξ) α X + t • dCo (smLie Ξ) β X := rfl
    rw [e, dCo_apply, dCo_apply, dCo_apply]
    simp only [ap, map_add (f := _), map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact mem_tens.1 (span_le_tens (N := levFnSub U Ξ) (fun φ h => h) (hα.val X)) i
  · rw [app_apply, cmp_rTensor]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.locInt :
    UpperTheory.V.Cj.H.LocInt := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _
  refine ⟨fun F => ?_, fun C hC => ?_⟩
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2
  · have hfin := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    refine ⟨hfin.toFinset.card, fun g => ?_⟩
    by_cases hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty
    · obtain ⟨γ0, hγ0⟩ := hne
      calc {γ : Γ | ↑γ * g ∈ C}.encard ≤ {δ : Γ | ↑δ ∈ C * C⁻¹}.encard := by
            apply Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)
            · intro γ hγ
              refine ⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩
              simp [mul_assoc]
            · intro a _ b _ h
              simpa using h
        _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocLimMul
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) : Module.End ℂ (Sm E a) :=
  (mulChi a χ).symm.toLinearMap ∘ₗ T ∘ₗ (mulChi a χ).toLinearMap

private theorem mul_cj (χ : HChar E) (T : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    mulChi a χ (cj χ T φ) = T (mulChi a χ φ) := (mulChi a χ).apply_symm_apply _

private theorem isOp_cj {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) {N : Submodule ℂ (Sm E a)}
    {T : Module.End ℂ (Sm E a)} (hT : IsOp N T) : IsOp (N.comap (mulChi a χ).toLinearMap) (cj χ T) := by
  refine { maps := ?_, lie := ?_, rt := ?_ }
  · intro φ hφ
    change mulChi a χ (cj χ T φ) ∈ N
    rw [mul_cj]
    exact hT.maps _ hφ
  · intro X φ hφ
    apply (mulChi a χ).injective
    have h1 := hT.lie X _ hφ
    have h2 := hχ.2 X (cj χ T φ)
    change lie E a X (T (mulChi a χ φ)) = T (lie E a X (mulChi a χ φ)) at h1
    rw [mul_cj, h1, hχ.2, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul, mul_cj] at h2
    rw [mul_cj]
    exact (add_right_cancel h2).symm
  · intro g φ hφ
    apply (mulChi a χ).injective
    have h1 := hT.rt g _ hφ
    have h2 := rt_mulChi χ g (cj χ T φ)
    change rt E a g (T (mulChi a χ φ)) = T (rt E a g (mulChi a χ φ)) at h1
    rw [mul_cj, h1, rt_mulChi, map_smul, map_smul, map_smul] at h2
    rw [mul_cj]
    exact (smul_right_injective _ (chiDet a χ g).ne_zero h2).symm

private theorem shift_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) 0 X (mulChi a χ φ) = mulChi a χ (shift (lie E a) r X φ) := by
  rw [shift_apply, shift_apply, zero_mul, zero_smul, add_zero, hχ.2, LinearMap.add_apply, LinearMap.smul_apply,
    one_apply_eq_self, Complex.coe_smul]

private theorem casA_mul {r : ℝ} {χ : HChar E} (hχ : IsTw (a := a) r χ) (c : ℝ) {n : ℕ} (e : Fin n → Herm E a)
    (φ : Sm E a) : casA 0 c e (mulChi a χ φ) = mulChi a χ (casA r c e φ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self, map_sub, map_sum, map_smul, shift_mul hχ]

private theorem locLim_mul (χ : HChar E) {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim (fun k => mulChi a χ (f k)) (mulChi a χ φ)) : LocLim f φ := by
  intro C hC
  have hc : Continuous fun g : GA E a => (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (χ.2.1.comp Matrix.GeneralLinearGroup.continuous_det).inv
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have h1 := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
  intro ε hε
  have hp : 0 < |B| + 1 := by positivity
  filter_upwards [h1 (ε / (|B| + 1)) (by positivity)] with k hk g hg
  have h2 := hk g hg
  rw [dist_eq_norm, mulChi_apply, mulChi_apply, ← sub_mul, lt_div_iff₀ hp] at h2
  have e : φ.1 g - (f k).1 g = (φ.1 g - (f k).1 g) * (chiDet a χ g : ℂˣ) * (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) :=
    (Units.mul_inv_cancel_right _ _).symm
  rw [dist_eq_norm, e, norm_mul]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h2
  exact (hB g hg).trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))

end

theorem UpperTheory.V.Cj.H.twRes :
    UpperTheory.V.Cj.H.TwRes := by
  intro E _ _ _ a r χ hχ N n e c P Q S h
  refine ⟨cj χ P, fun k => cj χ (Q k), fun k => cj χ (S k), isOp_cj hχ h.opP, fun k => isOp_cj hχ (h.opQ k),
    fun k => isOp_cj hχ (h.opS k), fun k φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply (mulChi a χ).injective
    rw [map_sub, ← casA_mul hχ, mul_cj, mul_cj]
    exact h.res k _ hφ
  · apply (mulChi a χ).injective
    rw [map_zero, ← casA_mul hχ, mul_cj]
    exact h.ker _ hφ
  · apply locLim_mul χ
    simp only [mul_cj]
    exact h.lim _ hφ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ROpApply
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private noncomputable def rAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def rOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (rAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem rOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    rOp V d N = MulOpposite.op (rAlg V d Nᵀ) := rfl

private theorem qdet_stab {M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ M) (h : ∀ i j, ∀ m ∈ N, X i j m ∈ N) (u : ℂ) :
    ∀ m ∈ N, Formalism.REAL.qdet X u m ∈ N := by
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {z | ∀ m ∈ N, z m ∈ N}
      mul_mem' := fun hx hy m hm => hx _ (hy m hm)
      add_mem' := fun hx hy m hm => N.add_mem (hx m hm) (hy m hm)
      algebraMap_mem' := fun c m hm => N.smul_mem c hm }
  let Z : Fin n → Fin n → S := fun i j => ⟨X i j, h i j⟩
  have e : ((Formalism.REAL.qdet Z u : S) : Module.End ℂ M) = Formalism.REAL.qdet X u := mapQ S.val Z u
  rw [← e]
  exact (Formalism.REAL.qdet Z u).2

theorem UpperTheory.V.Cj.H.capSm :
    UpperTheory.V.Cj.H.CapSm := by
  intro E _ _ _ a Ξ τ u
  have hE : ∀ i j : Fin a, Eop (a := a) τ i j = eL (N := Module.End ℂ (Sm E a)) (lie E a) τ i j := fun _ _ => rfl
  have hc : cap (a := a) τ u = Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) := rfl
  refine ⟨?_, fun m hm => ?_, fun X => ?_, fun N hN => ?_⟩
  · let f : Module.End ℂ (Sm E a) →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
      Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)
    have hf : ∀ X, smA Ξ X = f (lie E a X) := fun _ => rfl
    have e : eL (smA Ξ) τ = fun i j => f (Eop (a := a) τ i j) := by
      funext i j
      simp only [hE, eL, hf, map_smul, map_sub]
    rw [e, ← mapQ, ← hc]
    rfl
  · have hd := (dualIff E a Ξ τ m).1 hm
    have hB : ∀ X, smB Ξ X = rAlg (Sm E a) Ξ.d (Ξ.dmat X) := fun X => smB_apply Ξ X
    have h := (mapQ (rOp (Sm E a) Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)).symm.trans
      (congrArg (rOp (Sm E a) Ξ.d) (hd.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, rOp (Sm E a) Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) = -MulOpposite.op (eL (smB Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, rOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.unop_smul, MulOpposite.unop_one]
  · rw [← UpperTheory.V.Cm.uC_capC, ← UpperTheory.V.Cm.uC_ιC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (UpperTheory.V.Cm.capC_mem_center τ u) _) (UpperTheory.V.Cm.uC E a)
  · rw [hc]
    refine qdet_stab N _ (fun i j φ hφ => ?_) _
    rw [hE]
    exact N.smul_mem _ (N.sub_mem (hN _ φ hφ) (N.smul_mem _ (hN _ φ hφ)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.RopComm
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.ropComm :
    UpperTheory.V.Cj.H.RopComm := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ T hT f hf F
  have hF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf F
  have hTF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf (T F)
  rw [hF.2, hTF.2]
  refine (T.integral_comp_comm hF.1).symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show T (f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) F) = f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) (T F)
  rw [map_smul, hT g F]
end

