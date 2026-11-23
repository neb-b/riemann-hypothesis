module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExponentialGrowthExclusion
section
namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion

open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_fd (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by
  let L : Submodule ℤ (X.Ψ → ℝ) := (X.periods la).toIntSubmodule
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (X.periods la))
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using RealEmbeddingCharacters.periods_span (X := X) (la := la)⟩
  haveI := ZLattice.module_free ℝ L
  haveI := ZLattice.module_finite ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := by
    show Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) = L
    rw [Module.Basis.ofZLatticeBasis_span]
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain b volume
    rw [hspan] at h
    exact h
  · exact pos_iff_ne_zero.2 (ZSpan.measure_fundamentalDomain_ne_zero b)
  · exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top

lemma integral_swap_of_bdd {m n : Type} [Fintype m] [Fintype n] {D : Set (m → ℝ)} {K : Set (n → ℝ)}
    (hD : volume D < ⊤) (hK : volume K < ⊤) {f : (m → ℝ) → (n → ℝ) → ℂ}
    (hf : Continuous (Function.uncurry f)) {M : ℝ} (hM : ∀ s t, ‖f s t‖ ≤ M) :
    ∫ s in D, ∫ t in K, f s t = ∫ t in K, ∫ s in D, f s t := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hD.ne
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.ne
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)

end

end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma mean_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ENNReal) (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (s : Set α) (F : α → ℂ) :
    (((c • μ) s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂(c • μ) = ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
  have hc' : ((c.toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [Measure.restrict_smul, integral_smul_measure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, Complex.ofReal_mul, mul_inv, Complex.real_smul]
  calc _ = ((μ s).toReal : ℂ)⁻¹ * (∫ y in s, F y ∂μ) *
        (((c.toReal : ℝ) : ℂ)⁻¹ * ((c.toReal : ℝ) : ℂ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc', mul_one]

lemma mean_haar {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (s : Set G) (F : G → ℂ) :
    ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ = ((ν s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂ν := by
  haveI : ProperSpace G := FiniteDimensional.proper_real G
  have h := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  rw [h, ENNReal.smul_def]
  exact (mean_smul μ _ (ENNReal.coe_ne_zero.mpr hpos.ne') ENNReal.coe_ne_top s F).symm

variable (X : Data E r) (la : Wt X.Ψ r)

noncomputable def fjI (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℝ) : ℂ :=
  P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)

lemma flow_differentiable (ξ : Fin r → E) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun s : X.Ψ → ℂ => X.flow ξ s x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  intro s
  simp only [Data.flow, Matrix.mul_apply, Data.flowMat, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact (differentiable_apply τ) s

lemma fjI_continuous (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous (fjI X ξ ν P x) := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hc1 : Continuous (fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    (flow_differentiable X ξ x).continuous.comp
      (continuous_pi fun τ => Complex.continuous_ofReal.comp (continuous_apply τ))
  have hc2 : Continuous (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x)) :=
    hP.1.continuousOn.comp_continuous hc1 hmaps
  unfold fjI
  exact hc2.mul (by fun_prop)

lemma fjI_periodic (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξΛ : ξ ∈ X.Λ)
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ)
    (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (p : X.Ψ → ℝ) (hp : p ∈ X.periods la) (s : X.Ψ → ℝ) :
    fjI X ξ ν P x (p + s) = fjI X ξ ν P x s := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hadd : X.flow ξ (fun τ => (((p + s) τ : ℝ) : ℂ)) x =
      X.flow ξ (cR X p) (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    funext τ
    change X.flowMat ξ τ _ * mat x τ = X.flowMat ξ τ _ * mat (X.flow ξ _ x) τ
    rw [mat_flow, ← mul_assoc, flowMat_mul (X := X) hξ]
    congr 2
    simp [cR]
  unfold fjI
  rw [hadd, sec_periodic (X := X) la P hP hξΛ hξ hp _ (hmaps s)]
  congr 1
  obtain ⟨k, hk⟩ := hν p hp
  have hsplit : ∑ τ, (ν τ : ℂ) * (((p + s) τ : ℝ) : ℂ) =
      ∑ τ, (ν τ : ℂ) * (p τ : ℂ) + ∑ τ, (ν τ : ℂ) * (s τ : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.add_apply]
    push_cast
    ring
  rw [hsplit, mul_add, Complex.exp_add]
  have hk' : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (p τ : ℂ)) = 1 := by
    have h1 : ∑ τ, (ν τ : ℂ) * (p τ : ℂ) = (k : ℂ) / 2 := by
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) hk
      push_cast at h2
      linear_combination h2 / 2
    rw [h1, show -(4 * (Real.pi : ℂ) * I) * ((k : ℂ) / 2) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [hk', one_mul]

lemma exists_basis : ∃ ω : Module.Basis (Fin (Fintype.card X.Ψ)) ℝ (X.Ψ → ℝ),
    Submodule.span ℤ (Set.range ω) = perL X la := by
  classical
  let b := Module.Free.chooseBasis ℤ (perL X la)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (perL X la)) = Fintype.card X.Ψ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, perL_rank]
  refine ⟨(b.ofZLatticeBasis ℝ (perL X la)).reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem fj_eq_fourCoeff (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {n : ℕ} (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ))
    (hω : Submodule.span ℤ (Set.range ω) = perL X la) (ν : X.Ψ → ℝ) (k : Fin n → ℤ)
    (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) :
    X.fj la ξ ν P x = ReciprocityTheory.L2DbarEstimates.Y.fourCoeff
      (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)) 0 k := by
  classical

  have hper : X.periods la = (Submodule.span ℤ (Set.range ω)).toAddSubgroup := by
    rw [hω]
    rfl
  have hcond : ∀ p ∈ X.periods la, ∃ k' : ℤ, 2 * ∑ τ, ν τ * p τ = k' := by
    intro p hp
    rw [hper] at hp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
    refine ⟨∑ j, c j * k j, ?_⟩
    have hc : ∀ τ, (∑ j, c j • ω j) τ = ∑ j, (c j : ℝ) * ω j τ := fun τ => by
      simp [Finset.sum_apply, zsmul_eq_mul]
    simp only [hc]
    push_cast
    simp only [← hk, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hF0 : IsAddFundamentalDomain (X.periods la) (ZSpan.fundamentalDomain ω) volume := by
    rw [hper]
    exact ZSpan.isAddFundamentalDomain ω volume
  have hex : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ :=
    ⟨_, ZSpan.fundamentalDomain_measurableSet ω, hF0,
      pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero ω),
      (ZSpan.fundamentalDomain_isBounded ω).measure_lt_top⟩
  have hcount : ((X.periods la : Set (X.Ψ → ℝ))).Countable :=
    (Set.countable_range (fun c : Fin n → ℤ => ∑ j, c j • ω j)).mono fun p hp => by
      rw [hper] at hp
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
  haveI : Countable (X.periods la) := hcount.to_subtype
  unfold Data.fj
  rw [if_pos hcond, dite_eq_left hex]
  obtain ⟨-, hD, -, -⟩ := hex.choose_spec
  show ((volume hex.choose).toReal : ℂ)⁻¹ * ∫ s in hex.choose, fjI X ξ ν P x s = _

  rw [hD.measure_eq hF0, hD.setIntegral_eq hF0 (f := fjI X ξ ν P x)
    (fun g s => fjI_periodic X la P hP hξ.1 hξ.2.1 ν hcond hx g g.2 s)]

  set T := ω.equivFunL.symm with hTdef
  haveI : (Measure.map T volume).IsAddHaarMeasure := T.isAddHaarMeasure_map volume
  rw [mean_haar volume (Measure.map T volume) (ZSpan.fundamentalDomain ω) (fjI X ξ ν P x)]
  have hmp : MeasurePreserving T volume (Measure.map T volume) :=
    T.continuous.measurable.measurePreserving volume
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  rw [← hmp.setIntegral_preimage_emb hemb _ (ZSpan.fundamentalDomain ω),
    Measure.map_apply T.continuous.measurable (ZSpan.fundamentalDomain_measurableSet ω)]
  have hpre : T ⁻¹' ZSpan.fundamentalDomain ω = Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
    ext t
    have hTt : T t = ω.equivFun.symm t := rfl
    have hrep : ∀ i, ω.repr (ω.equivFun.symm t) i = t i := fun i => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [Set.mem_preimage, ZSpan.mem_fundamentalDomain, Set.mem_univ_pi, hTt]
    simp only [hrep]
  have hvol : volume (Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) = 1 := by
    rw [Real.volume_pi_Ico]
    simp
  have hae : (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) =ᵐ[volume]
      (Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1) := by
    rw [MeasureTheory.volume_pi]
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm
  rw [hpre, hvol, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_mul,
    setIntegral_congr_set hae]
  unfold ReciprocityTheory.L2DbarEstimates.Y.fourCoeff
  congr 1
  funext t
  have hT : ∀ τ, (T t) τ = ∑ j, t j * ω j τ := fun τ => by
    rw [show T t = ω.equivFun.symm t from rfl, Module.Basis.equivFun_symm_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hk' : ∀ j, (k j : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * (ω j τ : ℂ) := fun j => by
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) (hk j)
    push_cast at h2
    exact h2.symm
  unfold fjI
  simp only [hT, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, hk']
  push_cast
  congr 1
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField InfinitePlace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integerApproximationCount_holds : IntegerApproximationCount (E := E) := by
  intro r X
  refine ⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩
  classical
  have hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ h
    have := X.cmType (ComplexEmbedding.conjugate φ)
    rw [TraceIntegralBasis.conj_conj] at this
    exact this.mpr h
  let Z : TraceIntegralBasis.VS E := WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E =>
    if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
    else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))
  obtain ⟨α, hα⟩ := RingOfIntegersCovering.cover_OE Z
  refine ⟨α, fun τ => ?_⟩
  set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw
  have hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have h := PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w
    rw [PiLp.sub_apply, TraceIntegralBasis.iota_apply] at h
    exact h.trans hα
  have hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
      else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩) := rfl
  have hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1 := mk_embedding _
  rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
  · have hmem : w.1.embedding ∈ X.Ψ := h ▸ τ.2
    have hZ : Z w = w' τ := by
      rw [hZw, dite_eq_left hmem]
      congr 1
      exact Subtype.ext h
    rw [hZ, h] at hcoord
    rwa [norm_sub_rev] at hcoord
  · have hnot : w.1.embedding ∉ X.Ψ := by
      intro hm
      exact ((X.cmType _).mp hm) (h ▸ τ.2)
    have hZ : Z w = conj (w' τ) := by
      rw [hZw, dite_eq_right hnot]
      congr 2
      exact Subtype.ext h
    have hemb : w.1.embedding (α : E) = conj (τ.1 (α : E)) := by
      rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rw [hZ, hemb, ← map_sub, Complex.norm_conj] at hcoord
    rwa [norm_sub_rev] at hcoord

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMax
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def NonvanishingNearHalfMax : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 x0 : Frame X.Ψ r) (w : ℝ),
    X.IsSec la P → z0 ∈ X.dom → X.IsOrtho x0 → (∃ b ∈ Bor X.Ψ r, x0 = rmul z0 b) →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r →
    ∀ Z : X.Coord, X.zN Z ≤ frameRadius w r / 5 → P (X.xZ x0 Z) ≠ 0

def FrameAtHalfMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 : Frame X.Ψ r) (laStar w : ℝ),
    X.IsSec la P → z0 ∈ X.dom →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r → 0 < laStar → laStar ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (x : Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.dom ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar (3 * frameRadius w r / 5)) x lam ∧
      P x ≠ 0 ∧ ∀ τ v, X.maj x τ v ≤ 2 * X.maj z0 τ v

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalComplementLines
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_sub_left_of_ringHom (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma ppos_sub (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  simp only [Data.ppos, hermC_sub_left_of_ringHom, sub_mul, Finset.sum_sub_distrib, sub_smul]

variable {X : Data E r}

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UMatUpper
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

def blk (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Matrix (Fin c) (Fin c) ℂ :=
  G.submatrix (Fin.castLE c.isLt.le) (Fin.castLE c.isLt.le)

def rowc (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Fin c → ℂ := fun m => G c (Fin.castLE c.isLt.le m)

def uMat (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j c => if j = c then 1 else
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ else 0

lemma uMat_diag (G : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : uMat G j j = 1 := by
  simp [uMat]

lemma uMat_upper (G : Matrix (Fin n) (Fin n) ℂ) : (uMat G).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  simp only [uMat, Matrix.of_apply]
  rw [if_neg (ne_of_gt hij), dif_neg (not_lt.2 hij.le)]

lemma uMat_term (G : Matrix (Fin n) (Fin n) ℂ) (c m j : Fin n) :
    uMat G j c * G j m = (if j = c then G c m else 0) +
      (if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0) := by
  simp only [uMat, Matrix.of_apply]
  by_cases h1 : j = c
  · subst h1
    simp
  · by_cases h2 : j < c
    · simp [h1, h2]
    · simp [h1, h2]

lemma uT_G_zero (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (hdet : (blk G c).det ≠ 0) (m : Fin n)
    (hm : m < c) : ((uMat G)ᵀ * G) c m = 0 := by
  have hinv : IsUnit (blk G c).det := isUnit_iff_ne_zero.2 hdet
  have key : ∀ m' : Fin c, ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * blk G c j' m' =
      rowc G c m' := by
    intro m'
    have h := congrFun (Matrix.vecMul_vecMul (rowc G c) (blk G c)⁻¹ (blk G c)) m'
    rw [Matrix.nonsing_inv_mul _ hinv, Matrix.vecMul_one] at h
    rw [← h]
    rfl
  let g : Fin n → ℂ := fun j =>
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0
  have hmain : ((uMat G)ᵀ * G) c m = G c m + ∑ j : Fin n, g j := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, uMat_term, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  have hA : ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') =
      -∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have h : Fin.castLE c.isLt.le j' < c := j'.isLt
    simp only [g, dif_pos h]
    exact neg_mul _ _
  have hB : ∑ j : Fin n, g j = ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') := by
    rw [show (∑ j' : Fin c, g (Fin.castLE c.isLt.le j')) =
        ∑ x ∈ Finset.univ.map (Fin.castLEEmb c.isLt.le), g x from
      (Finset.sum_map Finset.univ (Fin.castLEEmb c.isLt.le) g).symm]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hjc : ¬ j < c := by
      intro hlt
      exact hj (Finset.mem_map.2 ⟨⟨j, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp only [g, dif_neg hjc]
  have k2 : ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m =
      G c m := key ⟨m, hm⟩
  rw [hmain, hB, hA, k2]
  ring

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end

