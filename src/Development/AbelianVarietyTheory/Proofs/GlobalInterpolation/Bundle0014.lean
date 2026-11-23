module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0012
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContDensityOnEqFibreMass
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem eq_zero_of_setIntegral_compact_eq_zero {K : Type} [MetricSpace K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] {B : Set K} (hB : IsOpen B) {h : K → ℂ} (hc : ContinuousOn h B)
    (hz : ∀ S : Set K, IsCompact S → S ⊆ B → ∫ b in S, h b ∂ν = 0) {t : K} (ht : t ∈ B) :
    h t = 0 := by
  by_contra hne
  have hpos : 0 < ‖h t‖ := norm_pos_iff.2 hne
  have hca : ContinuousAt h t := hc.continuousAt (hB.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hca (‖h t‖ / 2) (half_pos hpos)
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hB t ht
  have hρ0 : 0 < min (ε / 2) (δ / 2) := lt_min (half_pos hε) (half_pos hδ)
  have hmemS : ∀ b ∈ Metric.closedBall t (min (ε / 2) (δ / 2)), dist b t < ε ∧ dist b t < δ := by
    intro b hb
    have hb' := Metric.mem_closedBall.1 hb
    constructor
    · linarith [min_le_left (ε / 2) (δ / 2)]
    · linarith [min_le_right (ε / 2) (δ / 2)]
  have hSc := isCompact_closedBall t (min (ε / 2) (δ / 2))
  have hSB : Metric.closedBall t (min (ε / 2) (δ / 2)) ⊆ B := fun b hb =>
    hδB (Metric.mem_ball.2 (hmemS b hb).2)
  have hνS : 0 < ν (Metric.closedBall t (min (ε / 2) (δ / 2))) :=
    Metric.measure_closedBall_pos ν t hρ0
  have hνSf : ν (Metric.closedBall t (min (ε / 2) (δ / 2))) < ⊤ := hSc.measure_lt_top
  have hIh : IntegrableOn h (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    (hc.mono hSB).integrableOn_compact hSc
  have hIc : IntegrableOn (fun _ => h t) (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    integrableOn_const hνSf.ne
  have key := integral_sub hIh hIc
  rw [hz _ hSc hSB, setIntegral_const, zero_sub] at key
  have hbound := norm_setIntegral_le_of_norm_le_const hνSf (f := fun b => h b - h t)
    (C := ‖h t‖ / 2) (fun b hb => by rw [← dist_eq_norm]; exact (hball (hmemS b hb).1).le)
  rw [key, norm_neg, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hbound
  have hreal : 0 < ν.real (Metric.closedBall t (min (ε / 2) (δ / 2))) := by
    rw [measureReal_def]; exact ENNReal.toReal_pos hνS.ne' hνSf.ne
  nlinarith [mul_pos hreal hpos]

theorem contDensityOn_eq_fibre_mass : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by
  intro K V _ _ _ _ _ _ _ _ μ ν _ q hq fib hfib L hLc hLo g hg t ht
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  obtain ⟨hgc, hgS⟩ := hg
  have hLm : MeasurableSet L := hLo.measurableSet
  have hBo : IsOpen {t : K | t ≠ 0} := isOpen_ne
  have hφc : Continuous (L.indicator (1 : V → ℝ)) :=
    IsClopen.continuous_indicator ⟨hLc.isClosed, hLo⟩ continuous_const
  have hφs : HasCompactSupport (L.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨hint, hcont⟩ := hf3 _ hφc hφs (Set.subset_univ _)
  have hm_eq : (fun b => ∫ v, L.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b L).toReal := by
    funext b; rw [integral_indicator_one hLm]; rfl
  have hmc : ContinuousOn (fun b => (fib b L).toReal) {t : K | t ≠ 0} := by
    rw [← hm_eq]; exact hcont
  have hfin : ∀ b ∈ {t : K | t ≠ 0}, fib b L < ⊤ := by
    intro b hb
    have hi := hint b hb
    rw [integrable_indicator_iff hLm] at hi
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 hi).resolve_left (by simp)
  have hmcC : ContinuousOn (fun b => (((fib b L).toReal : ℝ) : ℂ)) {t : K | t ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn hmc
  have key : ∀ S : Set K, IsCompact S → S ⊆ {t : K | t ≠ 0} →
      ∫ b in S, (g b - (((fib b L).toReal : ℝ) : ℂ)) ∂ν = 0 := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    rw [integral_sub ((hgc.mono hSB).integrableOn_compact hS)
      ((hmcC.mono hSB).integrableOn_compact hS), sub_eq_zero, ← hgS S hS hSB, Set.image_id]
    have hind : L.indicator (1 : V → ℂ) = L.indicator (fun _ => (1 : ℂ)) := rfl
    rw [hind, integral_indicator_const _ hLm, integral_complex_ofReal, Complex.real_smul, mul_one]
    congr 1
    have haem : AEMeasurable (fun b => fib b L) (ν.restrict S) :=
      ((hmc.mono hSB).aemeasurable hSm).ennreal_ofReal.congr
        ((ae_restrict_mem hSm).mono fun b hb => ENNReal.ofReal_toReal (hfin b (hSB hb)).ne)
    rw [integral_toReal haem ((ae_restrict_mem hSm).mono fun b hb => hfin b (hSB hb)),
      measureReal_def, Measure.restrict_apply hLm]
    congr 1
    have hTm : MeasurableSet (L ∩ q ⁻¹' S) := hLm.inter (hq.measurable hSm)
    have h2 := hf2 ((L ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hTm)
    rw [Measure.restrict_univ, lintegral_indicator_one hTm] at h2
    rw [h2, ← lintegral_indicator hSm]
    refine lintegral_congr fun b => ?_
    rw [lintegral_indicator_one hTm]
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine measure_inter_conull (measure_mono_null (Set.compl_subset_compl.2 ?_) (hf1 b))
      intro v hv
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, id] at hv
      simp only [Set.mem_preimage, hv.1, hb]
    · rw [Set.indicator_of_notMem hb]
      refine measure_mono_null (fun v hv => ?_) (hf1 b)
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        id, Set.mem_univ, and_true]
      intro hqv
      exact hb (hqv ▸ hv.2)
  exact sub_eq_zero.1 (eq_zero_of_setIntegral_compact_eq_zero ν hBo (hgc.sub hmcC) key
    (show t ∈ {t : K | t ≠ 0} from ht))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
section
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaWeberRoad

def tpFactor (τ : ℍ) (z : ℂ) (n : ℕ) : ℂ :=
  (1 - cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ))) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * z)) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * z))

def TripleProduct : Prop := ∀ (τ : ℍ) (z : ℂ), HasProd (tpFactor τ z) (jacobiTheta₂ z τ)

def oddTheta (τ : ℍ) (z : ℂ) : ℂ :=
  cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ

theorem differentiable_oddTheta (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  intro z
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (w + 1 / 2))) z := by
    fun_prop
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w + ((τ : ℂ) + 1) / 2) z :=
    differentiableAt_id.add_const _
  have htheta : DifferentiableAt ℂ
      (fun w : ℂ => jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ) z := by
    have h0 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w τ) (z + ((τ : ℂ) + 1) / 2) :=
      differentiableAt_jacobiTheta₂_fst _ τ.2
    exact h0.comp z hshift
  exact hexp.mul htheta

end GlobalTheory.ThetaWeberRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding
section
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem exists_bruhat_function_closedEmbedding
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarGroupQuotientIntegralFormula
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact _root_.GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ hμ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarSubgroupQuotientIntegralFormula
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem fibreIntegral_smul (c : ℝ≥0) (ν : Measure H) [ν.IsMulLeftInvariant]
    [(c • ν).IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    fibreIntegral H (c • ν) f = fun q => (c : ℝ≥0∞) * fibreIntegral H ν f q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]
  rfl

theorem quotientFormula_smul [MeasurableSpace (G ⧸ H)] (c : ℝ≥0) (dg : Measure G)
    (ν : Measure H) [ν.IsMulLeftInvariant] [(c • ν).IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) : QuotientFormula H (c • dg) (c • ν) μ := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [fibreIntegral_smul]
  refine ⟨h1.const_mul _, ?_⟩
  rw [lintegral_const_mul _ h1, lintegral_smul_measure, h2]
  rfl

theorem eq_of_quotientFormula [MeasurableSpace (G ⧸ H)] {dg dg' : Measure G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) (h' : QuotientFormula H dg' ν μ) : dg = dg' := by
  ext s hs
  have hm : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]

end

theorem normaliseSubgroupClause : NormaliseSubgroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set G))
  have key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure],
      QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν := by
    intro ν ν' _ _ h h'
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩
    subst hc
    have h1 := eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
    have hK0 : dg K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
    have hKt : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
    have h2 : (c : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]
      have := congrArg (fun m : Measure G => m K) h1
      simpa using this
    have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp h2
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h4, one_smul]
  obtain ⟨dg₀, ⟨_, h₀⟩, -⟩ := _root_.GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH (Measure.haar : Measure H) μ hμ
  have hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀ :=
    Measure.isMulLeftInvariant_eq_smul dg dg₀
  have hpos : Measure.haarScalarFactor dg dg₀ ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'
  haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul _ hpos
  have h₁ : QuotientFormula H dg
      (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ := by
    have := quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀
    rwa [← hc] at this
  refine ⟨_, ⟨hν, h₁⟩, ?_⟩
  rintro ν ⟨_, h⟩
  exact key _ _ h₁ h

end GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
section
noncomputable section

namespace GlobalTheory.QuadFibre

open MeasureTheory
open scoped Pointwise

def IsSqrtOn {K : Type} [NormedField K] (U : Set K) (s : K → K) : Prop :=
  IsOpen U ∧ IsCompact U ∧ (1 : K) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧ (∀ a ∈ U, a⁻¹ ∈ U) ∧
    (∀ a ∈ U, ‖a‖ = 1) ∧ Continuous s ∧ ∀ a ∈ U, s a ^ 2 = a


open Classical in
def fibOf {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    (t : K) : Measure V := by
  classical
  exact if t = 0 then 0 else
    (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U)))

theorem fibOf_zero {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K) :
    fibOf μ ν q U s 0 = 0 := by simp [fibOf]

theorem fibOf_ne {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    {t : K} (ht : t ≠ 0) : fibOf μ ν q U s t =
      (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U))) := by
  simp [fibOf, ht]

end GlobalTheory.QuadFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IneLeFixingSubgroup
section
open NumberField IsDedekindDomain

namespace GlobalTheory.UnramDiscr


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω)
    {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact y.2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.UnramDiscr.embedding_eq {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    (hd : ¬ A.valuation ((discr K : ℤ) : Ω) < 1)
    (f g : K →+* Ω) (h : ∀ x : 𝓞 K, A.valuation (f x - g x) < 1) : f = g := by
  classical
  by_contra hfg
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, ← RingOfIntegers.rank K, Module.finrank_eq_card_chooseBasisIndex]
  let e : ι ≃ (K →ₐ[ℚ] Ω) := Fintype.equivOfCardEq hcard
  let b := integralBasis K
  have hint : ∀ (φ : K →+* Ω) (x : 𝓞 K), φ x ∈ A := fun φ x =>
    _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral A
      ((RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom)
  let N : Matrix ι ι A := Matrix.of fun i j => ⟨e j (b i), by
    rw [integralBasis_apply]; exact hint (e j).toRingHom _⟩
  have hM : ((discr K : ℤ) : Ω) = ((N.det ^ 2 : A) : Ω) := by
    have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b e
    rw [← coe_discr] at hdet
    have hN : A.subtype.mapMatrix N = Algebra.embeddingsMatrixReindex ℚ Ω b e := by
      ext i j
      simp [N, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [map_intCast, ← hN, ← RingHom.map_det] at hdet
    rw [hdet]
    simp
  have hF : f.toRatAlgHom ≠ g.toRatAlgHom := by
    intro hc
    apply hfg
    ext x
    exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) hc
  have hres : ((IsLocalRing.residue A).mapMatrix N).det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := e.symm f.toRatAlgHom) (j := e.symm g.toRatAlgHom)
    · simpa using hF
    · intro k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply]
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      simpa [b, integralBasis_apply] using h (RingOfIntegers.basis K k)
  rw [← RingHom.map_det, IsLocalRing.residue_eq_zero_iff] at hres
  apply hd
  rw [hM, ← A.valuation_lt_one_iff]
  exact Ideal.pow_mem_of_mem _ hres 2 (by norm_num)

end GlobalTheory.UnramDiscr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyUnivOfNullCone
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem isFibreFamily_univ_of_null_cone (K V : Type) [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (ν : Measure K) (q : V → K) (hq : Continuous q) (h0 : μ {x | q x = 0} = 0)
    (U : Set V) (B : Set K) (fib : K → Measure V) (hU : {x | q x ≠ 0} ⊆ U) (hB : {t | t ≠ 0} ⊆ B)
    (h : IsFibreFamily μ q id U ν B fib) :
    IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have hae : ∀ b, ∀ᵐ x ∂(fib b), q x = b := by
    intro b
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs _ => ?_⟩
  · refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx ⟨hx'.1, trivial⟩
  · have hμ : μ.restrict U = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      refine measure_mono_null ?_ h0
      intro x hx
      by_contra hx'
      exact hx (hU hx')
    rw [← h2 φ hφ, hμ, Measure.restrict_univ]
  · have key : ∀ b0 : K, b0 ≠ 0 → ∃ D : Set K, D ∈ nhds b0 ∧ b0 ∈ D ∧ D ⊆ B ∧
        (∀ b ∈ D, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) D := by
      intro b0 hb0
      have hr : 0 < ‖b0‖ := norm_pos_iff.mpr hb0
      have hD : IsClopen (Metric.ball b0 ‖b0‖) := IsUltrametricDist.isClopen_ball b0 _
      set D := Metric.ball b0 ‖b0‖ with hDdef
      have hD0 : ∀ t ∈ D, t ≠ 0 := by
        rintro t ht rfl
        simp [hDdef] at ht
      have hE : IsClopen (q ⁻¹' D) := hD.preimage hq
      let ψ : V → ℝ := (q ⁻¹' D).indicator φ
      have hψc : Continuous ψ := hE.continuous_indicator hc
      have hψs : HasCompactSupport ψ := by
        refine hcs.mono ?_
        intro x hx hx'
        apply hx
        simp [ψ, Set.indicator, hx']
      have hψt : tsupport ψ ⊆ U := by
        have : tsupport ψ ⊆ q ⁻¹' D :=
          closure_minimal Set.support_indicator_subset hE.isClosed
        intro x hx
        exact hU (hD0 _ (this hx))
      obtain ⟨hi, hco⟩ := h3 ψ hψc hψs hψt
      have hDB : D ⊆ B := fun t ht => hB (hD0 t ht)
      have heq : ∀ b ∈ D, ψ =ᵐ[fib b] φ := by
        intro b hb
        filter_upwards [hae b] with x hx
        have : x ∈ q ⁻¹' D := by
          show q x ∈ D
          rw [hx]; exact hb
        simp [ψ, Set.indicator_of_mem this]
      refine ⟨D, Metric.ball_mem_nhds _ hr, Metric.mem_ball_self hr, hDB, fun b hb => ?_, ?_⟩
      · exact (integrable_congr (heq b hb)).mp (hi b (hDB hb))
      · refine (hco.mono hDB).congr fun b hb => ?_
        exact (integral_congr_ae (heq b hb)).symm
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨D, -, hbD, -, hi, -⟩ := key b hb
      exact hi b hbD
    · obtain ⟨D, hD, -, -, -, hco⟩ := key b hb
      exact (hco.continuousAt hD).continuousWithinAt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExpStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_eq_polar_sqrt : ∀ (ε c : ℝ), (ε = 1 ∨ ε = -1) → ∀ g : ℂ → ENNReal, Measurable g → g 0 = 0 → ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (2 : ENNReal)⁻¹ * g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | exact GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | (intros; apply GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp <;> assumption)
end

