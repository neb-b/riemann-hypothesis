module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedProductMeasureCountable
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.AbsProd

theorem lintegral_prod_infinitePi {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (P : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (P i)] (S : Finset ι)
    (f : ∀ i, V i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂(Measure.infinitePi P) = ∏ i ∈ S, ∫⁻ y, f i y ∂(P i) := by
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun S (fun i (Y : ∀ i, V i) => f i (Y i))
    (ProbabilityTheory.iIndepFun_infinitePi (P := P) hf)
    (fun i => (hf i).comp (measurable_pi_apply i))]
  exact Finset.prod_congr rfl fun i _ =>
    (measurePreserving_eval_infinitePi P i).lintegral_comp (hf i)

theorem tail_split {ι : Type} [DecidableEq ι] (c : ι → ℝ) (hs : Summable fun i => |c i - 1|)
    {T S : Finset ι} (h : T ⊆ S) :
    ∏' i : {i : ι // i ∉ T}, c i.1 = (∏ i ∈ S \ T, c i) * ∏' i : {i : ι // i ∉ S}, c i.1 := by
  have key : ∀ U : Finset ι, ∏' i : {i : ι // i ∉ U}, c i.1 = ∏' i, (if i ∈ U then 1 else c i) := by
    intro U
    have := tprod_subtype {i | i ∉ U} c
    refine this.trans (tprod_congr fun i => ?_)
    by_cases hi : i ∈ U <;> simp [Set.mulIndicator, hi]
  have hm : Multipliable fun i => (if i ∈ S then 1 else c i) := by
    have h1 : Summable fun i => (if i ∈ S then (0 : ℝ) else c i - 1) := by
      refine Summable.of_norm_bounded hs fun i => ?_
      by_cases hi : i ∈ S <;> simp [hi]
    refine (Real.multipliable_one_add_of_summable h1).congr fun i => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  have hf : HasProd (fun i => if i ∈ S \ T then c i else 1) (∏ i ∈ S \ T, c i) := by
    have := hasProd_prod_of_ne_finset_one (f := fun i => if i ∈ S \ T then c i else 1)
      (s := S \ T) (L := SummationFilter.unconditional ι) (fun b hb => if_neg hb)
    rwa [Finset.prod_congr rfl (fun i hi => if_pos hi)] at this
  rw [key, key, ← hf.tprod_eq, ← hf.multipliable.tprod_mul hm]
  refine tprod_congr fun i => ?_
  by_cases hT : i ∈ T
  · simp [hT, h hT]
  · by_cases hS : i ∈ S <;> simp [hT, hS]

theorem exists_piece {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (a : ∀ i, Measure (V i)) (hσ : ∀ i, SigmaFinite (a i)) (T : Finset ι) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hs : Summable fun i => |c i - 1|)
    (ha : ∀ i ∉ T, a i Set.univ = ENNReal.ofReal (c i)) :
    ∃ ν : Measure (∀ i, V i), SFinite ν ∧ ∀ S : Finset ι, T ⊆ S → ∀ f : ∀ i, V i → ℝ≥0∞,
      (∀ i, Measurable (f i)) → ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂ν =
        (∏ i ∈ S, ∫⁻ y, f i y ∂(a i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, c i.1) := by
  classical
  by_cases h0 : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, inferInstance, fun S hS f _ => ?_⟩
    rw [lintegral_zero_measure]
    by_cases hiS : i ∈ S
    · rw [Finset.prod_eq_zero hiS (by simp [hi]), zero_mul]
    · have h1 := ha i (fun h => hiS (hS h))
      have h2 : c i = 0 := by
        rw [hi] at h1
        exact le_antisymm (ENNReal.ofReal_eq_zero.1 h1.symm) (hc0 i)
      rw [tail_split c hs (Finset.subset_insert i S),
        Finset.prod_eq_zero (s := insert i S \ S) (i := i) (by simp [hiS]) h2]
      simp
  push Not at h0
  have hP : ∀ i, ∃ (P : Measure (V i)) (g : V i → ℝ≥0∞), IsProbabilityMeasure P ∧ Measurable g ∧
      (i ∉ T → ∀ y, g y = 1) ∧ ∀ f : V i → ℝ≥0∞, Measurable f →
        ∫⁻ y, f y ∂(a i) = (if i ∈ T then 1 else ENNReal.ofReal (c i)) * ∫⁻ y, g y * f y ∂P := by
    intro i
    haveI : NeZero (a i) := ⟨h0 i⟩
    by_cases hi : i ∈ T
    · refine ⟨(a i).toFinite, (a i).rnDeriv (a i).toFinite, inferInstance,
        Measure.measurable_rnDeriv _ _, fun h => (h hi).elim, fun f hf => ?_⟩
      rw [if_pos hi, one_mul]
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq (a i) (a i).toFinite
        (absolutelyContinuous_toFinite _)]
      rw [lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hf]
      rfl
    · haveI : IsFiniteMeasure (a i) := ⟨by rw [ha i hi]; exact ENNReal.ofReal_lt_top⟩
      refine ⟨(a i Set.univ)⁻¹ • a i, fun _ => 1, inferInstance, measurable_const,
        fun _ _ => rfl, fun f _ => ?_⟩
      rw [if_neg hi, ← ha i hi, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simpa using h0 i) (measure_ne_top _ _)]
      simp
  choose P g hP hg hg1 hint using hP
  have hG : Measurable fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i) :=
    (Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_apply i)).const_mul _
  refine ⟨(Measure.infinitePi P).withDensity
    (fun Y => ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)),
    inferInstance, fun S hS f hf => ?_⟩
  have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hF]
  have h1 : ∀ Y : ∀ i, V i, ((fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)) *
      fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i)) Y =
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ S, (g i (Y i) * f i (Y i)) := by
    intro Y
    rw [Pi.mul_apply, Finset.prod_mul_distrib, mul_assoc,
      Finset.prod_subset hS (fun i _ hi => hg1 i hi (Y i))]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_prod_infinitePi P S (fun i y => g i y * f i y) (fun i => (hg i).mul (hf i)),
    Finset.prod_congr rfl (fun i _ => hint i (f i) (hf i)), Finset.prod_mul_distrib,
    tail_split c hs hS, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hc0 i),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hc0 i)]
  have h2 : ∏ i ∈ S, (if i ∈ T then 1 else ENNReal.ofReal (c i)) =
      ∏ i ∈ S \ T, ENNReal.ofReal (c i) := by
    rw [← Finset.prod_subset (Finset.sdiff_subset (s := S) (t := T))
      (fun i hi hi' => if_pos (by simpa [hi] using hi'))]
    exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_sdiff.1 hi).2
  rw [h2]
  ring

theorem exists_restricted_product : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  intro ι _ V₀ _ V _ L m₀ m h₀ hm hL hfin hs
  classical
  let a : Finset ι → ∀ i, Measure (V i) := fun T i =>
    (m i).restrict (if i ∈ T then (L i)ᶜ else L i)
  have hex := fun T : Finset ι => exists_piece (a T) (fun i => by dsimp only [a]; infer_instance) T
    (fun i => (m i (L i)).toReal) (fun i => ENNReal.toReal_nonneg) hs
    (fun i hi => by simp [a, hi, ENNReal.ofReal_toReal (hfin i)])
  choose ν hν hint using hex
  have hnull : ∀ (T : Finset ι) (i : ι) (N : Set (V i)), MeasurableSet N → a T i N = 0 →
      ν T {Y | Y i ∈ N} = 0 := by
    intro T i N hN h
    have hm' : ∀ j, Measurable (Function.update (fun j (_ : V j) => (1 : ℝ≥0∞)) i
        (N.indicator 1) j) := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact measurable_const.indicator hN
      · rw [Function.update_of_ne hj]
        exact measurable_const
    have h1 := hint T (insert i T) (Finset.subset_insert i T) _ hm'
    rw [Finset.prod_eq_zero (Finset.mem_insert_self i T)
      (by rw [Function.update_self, lintegral_indicator_one hN, h]), zero_mul] at h1
    have hN' : MeasurableSet {Y : ∀ i, V i | Y i ∈ N} := measurable_pi_apply i hN
    rw [← lintegral_indicator_one hN', ← h1]
    refine lintegral_congr fun Y => ?_
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj])
      (fun h => (h (Finset.mem_insert_self i T)).elim), Function.update_self]
    rfl
  let B : Finset ι → Set (∀ i, V i) := fun S => {Y | ∀ i ∉ S, Y i ∈ L i}
  have hB : ∀ S, MeasurableSet (B S) := by
    intro S
    have : B S = ⋂ i, ⋂ (_ : i ∉ S), {Y | Y i ∈ L i} := by ext; simp [B]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurable_pi_apply i (hL i)
  have hin : ∀ T S : Finset ι, T ⊆ S → ν T (B S)ᶜ = 0 := by
    intro T S h
    have : (B S)ᶜ = ⋃ i, ⋃ (_ : i ∉ S), {Y | Y i ∈ (L i)ᶜ} := by ext; simp [B]
    rw [this]
    refine measure_iUnion_null fun i => measure_iUnion_null fun hi => hnull T i _ (hL i).compl ?_
    have hT : i ∉ T := fun h' => hi (h h')
    simp [a, hT, Measure.restrict_apply (hL i).compl]
  have hout : ∀ T S : Finset ι, ¬ T ⊆ S → ν T (B S) = 0 := by
    intro T S h
    obtain ⟨i, hT, hS⟩ := Finset.not_subset.1 h
    refine measure_mono_null (t := {Y | Y i ∈ L i}) (fun Y hY => hY i hS) (hnull T i _ (hL i) ?_)
    simp [a, hT, Measure.restrict_apply (hL i)]
  refine ⟨m₀.prod (Measure.sum ν), ?_, fun S f₀ f hf₀ hf => ?_⟩
  · refine measure_mono_null (t := Set.univ ×ˢ ⋂ S, (B S)ᶜ) (fun Y hY => ?_) ?_
    · refine ⟨trivial, Set.mem_iInter.2 fun S hS => hY ?_⟩
      exact S.eventually_cofinite_notMem.mono fun i hi => hS i hi
    · rw [Measure.prod_prod, Measure.sum_apply_eq_zero.2
        (fun T => measure_mono_null (Set.iInter_subset _ T) (hin T T subset_rfl)), mul_zero]
  · have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    have e : {Y : V₀ × ∀ i, V i | ∀ i ∉ S, Y.2 i ∈ L i} = Set.univ ×ˢ B S := by ext; simp [B]
    rw [e, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_mul hf₀.aemeasurable hF.aemeasurable, mul_assoc]
    congr 1
    rw [Measure.restrict_sum _ (hB S), lintegral_sum_measure,
      tsum_eq_sum (s := S.powerset) (fun T hT => by
        rw [Measure.restrict_eq_zero.2 (hout T S (by simpa using hT)), lintegral_zero_measure])]
    have h1 : ∀ i ∈ S, ∫⁻ y, f i y ∂(m i) =
        ∫⁻ y in (L i)ᶜ, f i y ∂(m i) + ∫⁻ y in L i, f i y ∂(m i) := fun i _ => by
      rw [add_comm, lintegral_add_compl _ (hL i)]
    rw [Finset.prod_congr rfl h1, Finset.prod_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ⊆ S := Finset.mem_powerset.1 hT
    rw [Measure.restrict_eq_self_of_ae_mem (s := B S) (hin T S hTS), hint T S hTS f hf,
      ← Finset.prod_sdiff hTS, mul_comm (∏ i ∈ S \ T, _)]
    congr 2
    · exact Finset.prod_congr rfl fun i hi => by simp [a, hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [a, (Finset.mem_sdiff.1 hi).2]

end GlobalTheory.GaugeEx.AbsProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibBasic

section General

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {f : V → X} {ν : Measure X} {B : Set X}

theorem lintegral_preimage {fib : X → Measure V} (hf : Measurable f)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ Set.univ := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [Set.indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_mem (by simpa [hv] using hbS) _
  · rw [Set.indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_notMem (by simpa [hv] using hbS) _

theorem finite_on_compacts [T2Space V] [LocallyCompactSpace V] [BorelSpace V]
    {fib : X → Measure V} (h : IsFibreFamily μ f id Set.univ ν B fib) {β : X} (hβ : β ∈ B) :
    IsFiniteMeasureOnCompacts (fib β) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨φ, h1, -, hc, h01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty _)
  have hi := (h.2.2 φ φ.continuous hc (Set.subset_univ _)).1 β hβ
  refine lt_of_le_of_lt (measure_mono ?_) (hi.measure_ge_lt_top (ε := 1) one_pos)
  intro v hv
  exact (h1 hv).ge

theorem eq_at [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [BorelSpace V]
    [BorelSpace X] [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {fib fib' : X → Measure V} (hf : Measurable f) (hB : IsOpen B)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (h' : IsFibreFamily μ f id Set.univ ν B fib')
    {β : X} (hβ : β ∈ B) : fib β = fib' β := by
  haveI := finite_on_compacts h hβ
  haveI := finite_on_compacts h' hβ
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun g => ?_
  set φ : V → ℝ := fun v => (g v : ℝ) with hφdef
  have hφ : Continuous φ := NNReal.continuous_coe.comp g.continuous
  have hc : HasCompactSupport φ := HasCompactSupport.comp_left g.hasCompactSupport rfl
  have h0 : ∀ v, 0 ≤ φ v := fun v => (g v).2
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (Set.subset_univ _)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (Set.subset_univ _)
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[ν.restrict B]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable hB.measurableSet)
      (c'.aemeasurable hB.measurableSet) fun S hS _ => ?_
    rw [Measure.restrict_restrict hS,
      ← lintegral_preimage hf h _ hφm _ (hS.inter hB.measurableSet),
      ← lintegral_preimage hf h' _ hφm _ (hS.inter hB.measurableSet)]
  have e := Measure.eqOn_open_of_ae_eq hae hB c c' hβ
  simp only at e
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβ) (Filter.Eventually.of_forall h0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβ) (Filter.Eventually.of_forall h0)] at e
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg h0) (integral_nonneg h0)).1 e

end General

theorem continuous_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem fibAt_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J μ ν β m hν hβ hm
  obtain ⟨fib, h, rfl⟩ := hm
  haveI := hN.2.2.1
  have hB : IsOpen {c : R | IsUnit c} :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range
  refine ⟨?_, finite_on_compacts h hβ, ?_⟩
  · refine measure_mono_null ?_ (h.1 β)
    intro X hX hX'
    exact hX hX'.1
  · rintro m' ⟨fib', h', rfl⟩
    exact eq_at (continuous_qR σ R J).measurable hB h' h hβ

end GlobalTheory.GaugeEx.FibBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeProdFormula

theorem card_residue (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  obtain ⟨a, ha⟩ := GlobalTheory.HaarLatticeScale.exists_valued_eq_exp F v (-1)
  have ha1 : a ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp _).2 ha.le).le
  have h := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 ⟨a, ha1⟩ 1
    (by simpa using ha)
  have e : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {⟨a, ha1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v
      (by change Valued.v a ≠ 0; rw [ha]; exact WithZero.exp_ne_zero)]
    change _ ↔ _ ≤ Valued.v a
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  rw [pow_one, ← e] at h
  exact h

theorem modu_finite (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v)
    (hx : x ≠ 0) : (modu (Fv F v) x : ℝ) = ‖x‖ := by
  have hu : IsUnit x := hx.isUnit
  have hv : Valued.v x ≠ 0 := by simpa using hx
  let μ : Measure (Fv F v) := Measure.addHaar
  have h := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v (Fv F v) μ Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm (WithZero.log (Valued.v x))
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have e0 : (v.adicCompletionIntegers F : Set (Fv F v)) = Metric.closedBall 0 1 := by
    ext y
    rw [mem_closedBall_zero_iff, Valued.toNormedField.norm_le_one_iff]
    rfl
  have h0 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
  have h1 : μ (v.adicCompletionIntegers F : Set (Fv F v)) ≠ ∞ := by
    rw [e0]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  have e1 : {y : Fv F v | ∀ i, Valued.v ((ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i) ≤
      WithZero.exp (WithZero.log (Valued.v x))} = hu.unit • (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, WithZero.exp_log hv, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, IsUnit.unit_spec, inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
    simp
  have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp
  rw [e1, e2, Measure.real, ← distribHaarChar_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, card_residue,
    Fintype.card_unit, pow_one] at h
  have h2 := mul_right_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h
  rw [modu, dite_eq_left hu, h2, FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  push_cast
  congr 1

theorem distribHaarChar_pi_real (ι : Type) [Fintype ι] (u : (ι → ℝ)ˣ) :
    (distribHaarChar (ι → ℝ) u : ℝ) = ∏ i, |(u : ι → ℝ) i| := by
  have hu : ∀ i, (u : ι → ℝ) i ≠ 0 := fun i => ((Pi.isUnit_iff.1 u.isUnit) i).ne_zero
  have hp : (volume : Measure (ι → ℝ)) (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]; simp
  have e : u • (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) =
      Set.univ.pi fun i => (u : ι → ℝ) i • Set.Icc (0 : ℝ) 1 := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hu i), Units.smul_def, smul_eq_mul, smul_eq_mul, Pi.mul_apply]
    have : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i = ((u : ι → ℝ) i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrFun u.inv_mul i)
    rw [this]
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) (r := ∏ i, ‖(u : ι → ℝ) i‖₊) (by rw [hp]; simp) (by rw [hp]; simp)]
  · simp
  · rw [hp, e, volume_pi_pi, mul_one, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.addHaar_smul]
    rw [Module.finrank_self, pow_one, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
      ← Real.enorm_eq_ofReal_abs]
    rfl

theorem modu_infinite (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ainf F) (hx : IsUnit x) :
    (modu (Ainf F) x : ℝ) = ∏ w : InfinitePlace F, ‖x w‖ := by
  let r : Ainf F ≃+* (InfinitePlace F → ℝ) := RingEquiv.piCongrRight fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  let e : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { r.toAddEquiv with
      continuous_toFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
          (continuous_apply w)
      continuous_invFun := continuous_pi fun w =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
          (continuous_apply w) }
  have h := GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e hx.unit
    (Units.map (r : Ainf F →* (InfinitePlace F → ℝ)) hx.unit) (fun y => map_mul r x y)
  rw [modu, dite_eq_left hx, ← h, distribHaarChar_pi_real]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) (x w)

theorem prod_modu_eq_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  intro F _ _ _ e he
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), (modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ) =
      FinitePlace.equivHeightOneSpectrum.symm v e := fun v => by
    rw [modu_finite F v _ ((map_ne_zero _).2 he)]
    rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      modu (Fv F v) (algebraMap F (Fv F v) e)).Finite := by
    refine ((FinitePlace.hasFiniteMulSupport he).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn).subset fun v hv h => hv ?_
    apply NNReal.coe_injective
    rw [hf]
    exact h
  refine ⟨hfin, NNReal.coe_injective ?_⟩
  have h1 : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) : ℝ≥0) : ℝ) =
      ∏ᶠ w : FinitePlace F, w e := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [← hf]
    exact (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.map_finprod hfin
  rw [NNReal.coe_mul, h1, modu_infinite F _ (he.isUnit.map _), NNReal.coe_one, ← prod_abs_eq_one he]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 e)

end GlobalTheory.GaugeProdFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNorm
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem modu_eq_modu_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ u k hu hk
  obtain ⟨-, -, h2, hc⟩ := h
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hc, hc, star_star]
  have hss : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = _
      rw [hσ]
  let b : Module.Basis (Fin 2) R (R ⊗[F] E) :=
    Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)
  have hku : IsUnit k := by
    have h1 : IsUnit (algebraMap R (R ⊗[F] E) k) := by
      rw [hk]; exact hu.mul (hu.map _)
    have h3 := h1.map (Algebra.norm R)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin] at h3
    exact (isUnit_pow_iff two_ne_zero).1 h3
  refine ⟨hku, ?_⟩
  letI : StarRing (R ⊗[F] E) :=
    { star := sigR R σ
      star_involutive := hss
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add _ x y }
  haveI : ContinuousStar (R ⊗[F] E) := ⟨GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ⟩
  rw [modu, modu, dite_eq_left hu, dite_eq_left hku]
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm R (R ⊗[F] E) b.equivFun.symm
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap) hu.unit hku.unit hk

end GlobalTheory.GaugeEx
end

