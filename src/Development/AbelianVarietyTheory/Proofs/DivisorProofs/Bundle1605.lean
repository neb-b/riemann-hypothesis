module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.AdelicHaarPure

theorem measurableSet_box (F : Type) [Field F] [NumberField F] (κ : Type) [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSet {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} := by
  have : {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} =
      ⋂ v, ⋂ (_ : v ∉ S), ⋂ i, (fun y : κ → Af F => evalV F v (y i)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y; simp
  rw [this]
  refine IsClosed.measurableSet (isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => ?_)
  exact (Valued.isClosed_integer (v.adicCompletion F)).preimage ((GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i))

theorem evalV_add_singleFin_ne {F : Type} [Field F] [NumberField F] {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w)
    (a : Af F) (t : Fv F w) : evalV F v (a + singleFin w t) = evalV F v a := by
  rw [map_add (f := _), evalV_singleFin_ne h, add_zero]

theorem finPart (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (κ → Fv F v)] [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (κ → Fv F v)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure]
    (hμf : μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure]
    (hμv : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (f : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℝ≥0∞)
    (hf : ∀ v, Measurable (f v)) :
    ∫⁻ y, {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
        ∏ v ∈ S, f v (fun i => evalV F v (y i)) ∂μf = ∏ v ∈ S, ∫⁻ t, f v t ∂(μv v) := by
  classical
  have hcw : ∀ v, Measurable fun y : κ → Af F => fun i => evalV F v (y i) := fun v =>
    (continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i)).measurable
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    rw [lintegral_indicator_one (measurableSet_box F κ ∅), ← hμf]
    congr 1
    ext y
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Set.mem_setOf_eq]
    exact forall_comm
  | insert w S hw ih =>
    set K : (κ → Af F) → ℝ≥0∞ := fun y =>
      {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
        ∏ v ∈ S, f v (fun i => evalV F v (y i)) with hK
    have hKm : Measurable K :=
      (measurable_one.indicator (measurableSet_box F κ _)).mul
        (Finset.measurable_prod _ fun v _ => (hf v).comp (hcw v))
    have hKi : ∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y := by
      intro y t
      have h1 : ∀ v ∈ S, (fun i => evalV F v (y i + singleFin w (t i))) = fun i => evalV F v (y i) := fun v hv =>
        funext fun i => evalV_add_singleFin_ne (by rintro rfl; exact hw hv) _ _
      have h2 : ({y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1
          (fun i => y i + singleFin w (t i)) : ℝ≥0∞) =
          {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y := by
        have : ((fun i => y i + singleFin w (t i)) ∈
            {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}) ↔
            (y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}) := by
          simp only [Set.mem_setOf_eq]
          refine forall_congr' fun v => imp_congr_right fun hv => forall_congr' fun i => ?_
          rw [evalV_add_singleFin_ne (by rintro rfl; exact hv (Finset.mem_insert_self _ S))]
        by_cases hy : y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (this.2 hy)]; rfl
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (this.1 h))]
      simp only [hK, h2]
      congr 1
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    have hstep := _root_.GlobalTheory.HaarFactorOffPlace.lintegral_evalV_mul_shiftInvariant F κ w μf (μv w) (hμv w) K hKm hKi (f w) (hf w)
    have e1 : ∀ y : κ → Af F,
        {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ insert w S, f v (fun i => evalV F v (y i)) = f w (fun i => evalV F w (y i)) * K y := by
      intro y
      rw [Finset.prod_insert hw, hK]
      ring
    have hiff : ∀ y : κ → Af F, (∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F) ↔
        (∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F) ∧
          ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      intro y
      constructor
      · intro h
        exact ⟨h w hw, fun v hv => h v fun h' => hv (Finset.mem_insert_of_mem h')⟩
      · rintro ⟨h1, h2⟩ v hv
        by_cases hvw : v = w
        · subst hvw; exact h1
        · exact h2 v (by simp [hvw, hv])
    have e2 : ∀ y : κ → Af F, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1
        (fun i => evalV F w (y i)) * K y =
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ S, f v (fun i => evalV F v (y i)) := by
      intro y
      rw [hK, ← mul_assoc]
      congr 1
      by_cases h : y ∈ {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
      · have h' := (hiff y).1 h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (fun i => evalV F w (y i)) ∈
          {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} from h'.1),
          Set.indicator_of_mem (show y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
            from h'.2)]
        simp
      · rw [Set.indicator_of_notMem h]
        by_cases h1 : ∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F
        · have h2 : y ∉ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} :=
            fun h2 => h ((hiff y).2 ⟨h1, h2⟩)
          rw [Set.indicator_of_notMem h2, mul_zero]
        · rw [Set.indicator_of_notMem (show (fun i => evalV F w (y i)) ∉
            {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} from h1), zero_mul]
    simp_rw [e1]
    rw [hstep, Finset.prod_insert hw]
    simp_rw [e2]
    rw [ih]

theorem integral_pure_haar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [∀ v : Pl (F := F), MeasurableSpace (κ → Fv F v)] [∀ v : Pl (F := F), BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl (F := F), Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure],
    (∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), Continuous f → Integrable f μi → IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ = c * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v) := by
  intro F _ _ κ _ _ _ _ _ _ _ μ _ μi _ μv _ hμv
  classical
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : ∀ v : Pl (F := F), ProperSpace (Fv F v) := fun v => GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨μf, hμfH, hμf1⟩ := _root_.GlobalTheory.FinAdeleHaarNorm.exists_addHaar_integral_eq_one F κ
  obtain ⟨c, hc0, hctop, hc⟩ := _root_.GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul F κ μ μi μf
  refine ⟨(c.toReal : ℂ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hc0, hctop⟩), fun f φ hfc hfi hφ => ?_⟩
  have hfinS := Filter.eventually_cofinite.1 hφ.2
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, φ v = ind κ v := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hpi : Continuous fun x : κ → AF F => fun i => evI F (x i) :=
    continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  have hpv : ∀ v : Pl (F := F), Continuous fun x : κ → AF F => fun i => evFin F v (x i) := fun v =>
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_snd.comp (continuous_apply i))
  set B : Set (κ → AF F) := {x | ∀ v ∉ S, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F} with hB
  have hBm : MeasurableSet B := by
    have : B = (fun x : κ → AF F => fun i => sndA F (x i)) ⁻¹'
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} := rfl
    rw [this]
    have hsnd : Continuous (fun x : κ → AF F => fun i => sndA F (x i)) :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact hsnd.measurable (measurableSet_box F κ S)
  have hlin : ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (fv : ∀ v : Pl (F := F), (κ → Fv F v) → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x, fi (fun i => evI F (x i)) * ∏ v ∈ S, fv v (fun i => evFin F v (x i)) ∂(μ.restrict B) =
        (∫⁻ z, fi z ∂μi) * (∏ v ∈ S, ∫⁻ t, fv v t ∂(μv v)) * c := by
    intro fi fv hfi hfv
    rw [← lintegral_indicator hBm]
    have e : ∀ x : κ → AF F, B.indicator (fun x => fi (fun i => evI F (x i)) * ∏ v ∈ S, fv v (fun i => evFin F v (x i))) x =
        fi (fun i => evI F (x i)) *
          ({y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 (fun i => sndA F (x i)) *
            ∏ v ∈ S, fv v (fun i => evalV F v (sndA F (x i)))) := by
      intro x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (fun i => sndA F (x i)) ∈
          {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} from hx)]
        simp only [Pi.one_apply, one_mul]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (fun i => sndA F (x i)) ∉
          {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} from hx)]
        simp
    simp_rw [e]
    have hcw : ∀ v, Measurable fun y : κ → Af F => fun i => evalV F v (y i) := fun v =>
      (continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i)).measurable
    have hgm : Measurable fun y : κ → Af F =>
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ S, fv v (fun i => evalV F v (y i)) :=
      (measurable_one.indicator (measurableSet_box F κ S)).mul
        (Finset.measurable_prod _ fun v _ => (hfv v).comp (hcw v))
    rw [hc fi _ hfi hgm,
      finPart F κ μf hμf1 μv hμv S fv hfv]
    ring
  have hint : ∀ v, Integrable (φ v) (μv v) := fun v =>
    (hφ.1 v).1.continuous.integrable_of_hasCompactSupport (hφ.1 v).2
  obtain ⟨h1, h2⟩ := GlobalTheory.GaugeEx.ProdInt.integral_tensor (μ.restrict B) μi μv (fun x : κ → AF F => fun i => evI F (x i))
    (fun v x i => evFin F v (x i)) hpi.measurable (fun v => (hpv v).measurable) S c hctop hlin f φ hfi hint
  have hΦB : (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
      B.indicator fun x => f (fun i => evI F (x i)) * ∏ v ∈ S, φ v (fun i => evFin F v (x i)) := by
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      apply hv
      simp only [hout v hvS, ind]
      exact Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        hx v hvS) _
    · rw [Set.indicator_of_notMem hx]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, i, hv⟩ := hx
      have hev : ∀ᶠ v in Filter.cofinite, φ v (fun i => evFin F v (x i)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
          Filter.eventually_all.2 fun i => (sndA F (x i)).2
        filter_upwards [hφ.2, h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show (fun i => evFin F w (x i)) ∈ {x | ∀ i, x i ∈ w.adicCompletionIntegers F} from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉
          {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hv (h i)) _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  have hprod : ∏ᶠ v, ∫ x, φ v x ∂(μv v) = ∏ v ∈ S, ∫ x, φ v x ∂(μv v) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    intro v hv
    by_contra hvS
    apply hv
    have hm : MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
      have : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
          ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by ext; simp
      rw [this]
      exact (isClosed_iInter fun i => (Valued.isClosed_integer (v.adicCompletion F)).preimage (continuous_apply i)).measurableSet
    have := integral_indicator_const (μ := μv v) (1 : ℂ) hm
    simp only [hout v hvS, ind]
    simpa [Measure.real, Pi.one_def, hμv v] using this
  rw [hΦB, hprod]
  refine ⟨(integrable_indicator_iff hBm).2 h1, ?_⟩
  rw [integral_indicator hBm, h2]
  ring

end GlobalTheory.AdelicHaarPure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleSubTop
section
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PsCo.TrAdm

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.D.gk.HC GlobalTheory.HcPort Formalism.MainNotions.S

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kfSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ (smD ε σ) where
  carrier := KF ε σ
  add_mem' := by
    rintro a b ⟨S, hS, ha, hSK⟩ ⟨T, hT, hb, hTK⟩
    refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, fun g hg v hv => ?_⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hv
    rw [← hxy, map_add (f := _)]
    exact Submodule.add_mem_sup (hSK g hg x hx) (hTK g hg y hy)
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := fun c _ ⟨S, hS, ha, hSK⟩ => ⟨S, hS, by simpa using S.smul_mem c ha, hSK⟩

theorem kStableSub_iSup {ι : Type} {E : Fin n → Fin n → Module.End ℂ (smD ε σ)} (S : ι → Submodule ℂ (smD ε σ))
    (h : ∀ i, IsKStableSub ε E (S i)) : IsKStableSub ε E (⨆ i, S i) := by
  intro a b hab x hx
  refine Submodule.iSup_induction S (motive := fun x => E a b x ∈ ⨆ i, S i) hx (fun i y hy => ?_) ?_ ?_
  · exact Submodule.mem_iSup_of_mem i (h i a b hab y hy)
  · simp
  · intro y z hy hz; rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

end

theorem isAdmissibleSub_top (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : GlobalTheory.GKModule.IsAdmissibleSub ε σ ⊤ := by
  classical
  intro Λ
  have hD := isDerivedOn_smE hσ
  set A := {v : smD ε σ | v ∈ KF ε σ ∧ IsKHWVec ε (smE ε σ) Λ v}
  have hAf : FiniteDimensional ℂ (Submodule.span ℂ A) := uAdm n ε H σ hσ hirr Λ
  have hAK : Submodule.span ℂ A ≤ kfSub ε σ := Submodule.span_le.2 fun v hv => hv.1
  let b := Module.finBasis ℂ (Submodule.span ℂ A)
  let M : Submodule ℂ (smD ε σ) := ⨆ i, Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)
  have hbi : ∀ i, FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) ∧
      IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) := fun i =>
    kSpan_fin_B K_finite_smooth_vectors hσ hirr (hAK (b i).2)
  haveI : ∀ i, FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) := fun i => (hbi i).1
  have hMf : FiniteDimensional ℂ M := Submodule.finiteDimensional_iSup _
  have hMK : IsKStableSub ε (smE ε σ) M := kStableSub_iSup _ fun i => (hbi i).2
  have hAM : Submodule.span ℂ A ≤ M := by
    intro x hx
    have h1 := congrArg (fun z : Submodule.span ℂ A => (z : smD ε σ)) (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem i (Formalism.REAL.mem_compact_span_self _))
  let T : Submodule ℂ H := M.map (smD ε σ).subtype
  have hTf : FiniteDimensional ℂ T := Module.Finite.map _ _
  have hTK := kStable_of_isKStableSub hσ hD M hMf hMK
  refine Submodule.finiteDimensional_of_le (S₂ := T) (sSup_le fun S hS' => ?_)
  have hS := hS'.2
  obtain ⟨hSf, hSK, hirrS, -, -⟩ := id hS
  have hSD : S ≤ smD ε σ := fun v hv => (K_finite_smooth_vectors n ε H σ hσ hirr).1 v ⟨S, hSf, hv, hSK⟩
  obtain ⟨w, hwS, hw0, hwΛ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hS hSD
  have hwA : w ∈ A := ⟨⟨S, hSf, hwS, hSK⟩, hwΛ⟩
  have hwM : w ∈ M := hAM (Submodule.subset_span hwA)
  have hST : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ T) := by
    intro g hg v hv
    refine ⟨hSK g hg v hv.1, ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
    obtain ⟨z, hz, hzeq⟩ := hTK g hg y hy
    exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
  rcases hirrS _ inf_le_left hST with h0 | hEq
  · exfalso
    have hmem : (w : H) ∈ S ⊓ T := ⟨hwS, Submodule.mem_map_of_mem hwM⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hw0 (Subtype.ext hmem)
  · rw [← hEq]; exact inf_le_right

end GlobalTheory.PsCo.TrAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfUnitOffEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

theorem GlobalTheory.Square.isAwayUnit_of_unitOff_embedding : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (q m : ℕ), 0 < q → q ∣ m →
    GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q (σ x) → GlobalTheory.Square.IsAwayUnit m x := by
  intro K _ _ σ x q m hq hqm h
  obtain ⟨hx0, n, h1, h2⟩ := h
  have hx : x ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
  have hinj : Function.Injective σ.toIntAlgHom := σ.injective
  have i1 : (q : K) ^ n * x ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h1
  have i2 : (q : K) ^ n * x⁻¹ ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h2
  set a : 𝓞 K := ⟨_, i1⟩ with ha_def
  set b : 𝓞 K := ⟨_, i2⟩ with hb_def
  have ha : algebraMap (𝓞 K) K a = (q : K) ^ n * x := rfl
  have hb : algebraMap (𝓞 K) K b = (q : K) ^ n * x⁻¹ := rfl
  obtain ⟨d, rfl⟩ := hqm
  refine GlobalTheory.Square.AwayClosure.of_integral (k := n) (l := n) (a := a * (d : 𝓞 K) ^ n)
    (b := b * (d : 𝓞 K) ^ n) hx ?_ ?_
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, ha]
    push_cast
    ring
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, hb]
    push_cast
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem latLast_isLattice : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  intro E _ _ n N hN M L hM hL
  subst hN
  have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
  have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
  simp only [hiC, hiL] at hL
  let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
    { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
      map_add' := by
        intro x y; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      map_smul' := by
        intro a x; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
  have gC : ∀ x k, g x (Fin.castSucc k) = x k := fun x k => by simp [g]
  have gL : ∀ x, g x (Fin.last n) = 0 := fun x => by simp [g]
  let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
  have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [gC] using hm, 0, by simp [gL]⟩
  have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
  have dec : ∀ x : Fin (n + 1) → E, x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
    intro x; ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [gL, e]
    · simp [gC, e, Pi.single_apply, Fin.castSucc_ne_last]
  have hLeq : L = M.map (g.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {e} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvM, c, hc⟩ := (hL v).1 hv
      rw [dec v]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hvM))
        (Submodule.mem_sup_right ?_)
      have hs : (c : E) • e = c • e := algebraMap_smul E c e
      rw [← hc, hs]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
    · exact sup_le (Submodule.map_le_iff_le_comap.2 fun m hm => gm m hm)
        (Submodule.span_le.2 (by simpa using he))
  refine ⟨?_, ?_⟩
  · rw [hLeq]
    exact Submodule.FG.sup (hM.fg.map _) (Submodule.fg_span_singleton e)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigenStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  first | exact @GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | exact GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | (intros; apply GlobalTheory.DblVacEigen.local_identity_of_tens_eigen <;> assumption)
end

