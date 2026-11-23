module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartGlobalWhittakerCoefficient
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

noncomputable section

namespace GlobalTheory.JSW.WhitSmooth

open GroundTheory.Automorphic.FourierWhittaker GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_oneL (F : GA E a → ℂ) (g : GA E a) : chart F g (oneL E a) = F g := by
  have := chart_val F g 1
  simpa using this

theorem chart_whit (F : GA E a → ℂ) (g : GA E a) :
    chart (GlobalTheory.JSW.whit F) g = fun y => ∫ X in vecDomain E (Pos a),
      chart F (uGL X * g) y * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, GlobalTheory.JSW.WhitAlg.whit_eq, mul_assoc]
  · simp only [chart, dif_neg h, zero_mul, integral_zero]

theorem hasFDerivAt_chart_whit {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∫ X in vecDomain E (Pos a), (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
        fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) ∂vecMeasure E (Pos a)) (oneL E a) := by
  rw [chart_whit]
  have hy : oneL E a ∈ invSet E a := isUnit_one
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hm : Continuous fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a) :=
    ((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd
  have hmt : Set.MapsTo (fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a))
      (Set.univ ×ˢ invSet E a) (Set.univ ×ˢ invSet E a) := fun p hp => ⟨Set.mem_univ _, hp.2⟩
  have hc := h.continuousOn_fderiv.comp hm.continuousOn hmt
  have hc0 := h.continuousOn_chart.comp hm.continuousOn hmt
  obtain ⟨C, hC⟩ := (isCompact_closure_vecDomain.prod hS).exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono (Set.subset_univ _) hSU))
  have hint : ∀ z ∈ invSet E a, Integrable (fun X => chart φ.1 (uGL X * g) z *
      (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    fun z hz => ((((hc0.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨trivial, hz⟩)).mul
      GlobalTheory.JSW.WhitAlg.continuous_psiNeg).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set
      subset_closure
  have hint' : Integrable (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ((GlobalTheory.JSW.WhitAlg.continuous_psiNeg.smul (hc.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ => ⟨trivial, hy⟩)).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun z X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) • fderiv ℝ (chart φ.1 (uGL X * g)) z) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz => (hint z hz).1) (hint _ hy) hint'.1
    ?_ (integrable_const C) ?_
  · filter_upwards [ae_restrict_mem measurableSet_vecDomain] with X hX z hz
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC (X, z) ⟨subset_closure hX, hz⟩
  · refine .of_forall fun X z hz => ?_
    exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt.mul_const _

theorem hasFDerivAt_chart_whit' {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∑ i, GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g • coef i (oneL E a)) (oneL E a) := by
  refine (hasFDerivAt_chart_whit h g).congr_fderiv ?_
  have hy : oneL E a ∈ invSet E a := isUnit_one
  have e : ∀ X : Pos a → Ad E, (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) = ∑ i,
        (chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (uGL X * g) (oneL E a) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) • coef i (oneL E a) := fun X => by
    rw [fderiv_chart φ _ hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const, ← congrFun (chart_whit _ g) (oneL E a), chart_oneL]
  · have hl := h.lie (Module.finBasis ℝ (Lie E a) i)
    refine (Integrable.smul_const ?_ _)
    simp_rw [chart_oneL]
    exact GlobalTheory.JSW.WhitAlg.integrableOn_whit (ContAut.continuous_of_isOpen_stab E a _ hl.2) g

theorem whit_mem_Sm (φ : Sm E a) (h : Good φ) : GlobalTheory.JSW.whit φ.1 ∈ Sm E a := by
  refine GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt E a {f | ∃ ψ : Sm E a, Good ψ ∧ f = GlobalTheory.JSW.whit ψ.1} ?_ _
    ⟨φ, h, rfl⟩
  rintro f ⟨ψ, hψ, rfl⟩
  exact ⟨_, inferInstance, fun i => GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) ψ).1,
    fun i => coef i (oneL E a), fun i => ⟨_, hψ.lie _, rfl⟩, hasFDerivAt_chart_whit' hψ⟩

theorem whit_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  intro E _ _ _ a φ hφ g
  exact whit_mem_Sm φ ⟨hφ.left, hφ.level⟩ g

end GlobalTheory.JSW.WhitSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultiple
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspBound

theorem exists_mul_mem_closure {O K Ω : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field Ω] [Algebra K Ω] (S : Set Ω) {x : Ω} (hx : x ∈ Algebra.adjoin K S) :
    ∃ κ : O, κ ≠ 0 ∧ algebraMap K Ω (algebraMap O K κ) * x ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) := by
  have hmem : ∀ u : O, algebraMap K Ω (algebraMap O K u) ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) :=
    fun u => Subring.subset_closure (Or.inl ⟨u, rfl⟩)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    exact ⟨1, one_ne_zero, by rw [map_one, map_one, one_mul]; exact Subring.subset_closure (Or.inr hx)⟩
  | algebraMap r =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) r
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← map_mul, mul_div_cancel₀ _ hb0]
    exact hmem a
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x + y) =
        algebraMap K Ω (algebraMap O K t) * (algebraMap K Ω (algebraMap O K s) * x) +
        algebraMap K Ω (algebraMap O K s) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (hmem t) h1) (mul_mem (hmem s) h2)
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x * y) =
        (algebraMap K Ω (algebraMap O K s) * x) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact mul_mem h1 h2

theorem inV_iff' (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa' {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff', ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff', EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_mem_B {O : Type} [CommRing O] {β : O →+* c.F} (P : GlobalTheory.Reg.PChart Xo c β) {e : P.Ω} {T : CDVR}
    {io : c.F →+* T.Fr} (ψ : P.R e →+* T.Fr) (hψ : ∀ k, ψ (algebraMap c.F _ k) = io k) (hO : ∀ a, InV T (io (β a)))
    (hg : ∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) (s : P.R e) (hs : (s : P.Ω) ∈ P.B) : InV T (ψ s) := by
  have hle : P.B ≤ (((algebraMap T.V T.Fr).range.comap ψ).map (P.R e).val.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro w (⟨o, rfl⟩ | hw)
    · refine ⟨algebraMap c.F _ (β o), ?_, rfl⟩
      show ψ (algebraMap c.F _ (β o)) ∈ (algebraMap T.V T.Fr).range
      rw [hψ]; exact hO o
    · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hle hs
  obtain rfl : w = s := Subtype.ext hw'
  exact hw

end GlobalTheory.CuspBound

namespace GlobalTheory.CuspBound


set_option maxHeartbeats 1000000 in
theorem exists_bddAll_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
    obtain ⟨J, hJ, P, hC, hreg⟩ := _root_.GlobalTheory.CuspReg.exists_cover_noPole E H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
    haveI := Fintype.ofFinite J
    choose κ hκ0 hκ using fun j =>
      exists_mul_mem_closure (O := (la.valuation c.F).valuationSubring) (K := c.F) ((P j).gens : Set (P j).Ω) (hreg j)
    have hF := cusp_le_sec Xo c U a n hf
    refine ⟨algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j), ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective _ c.F)).2 (Finset.prod_ne_zero_iff.2 fun j _ => hκ0 j)
    intro T io m ho y _
    letI := io.toAlgebra
    obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
    let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
    have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
      ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
        by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
    have hO : ∀ a : (la.valuation c.F).valuationSubring, InV T (io (algebraMap _ c.F a)) := fun a => inV_of_overLa' ho a
    obtain ⟨j, e, he, ψ, z, t, hgW, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (hO a)) y.1
    have hzI : Integral T io z := (P j).int e he T io ψ (fun a => hO a) (fun g hg => (hW _).1 (hgW g hg)) z hz
    let z' : IntFr Xo c T io := ⟨z, hE.test _ z, hzI⟩
    set κ' := algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j) with hκ'
    rw [← evI_smul, inV_iff_of_frBor (Submodule.smul_mem _ κ' hF) y z' t ht, evI_smul]
    show InV T (io κ' * evR Xo c f z)
    rw [(hev _).1 _ ψ _ _ hz]
    let s : (P j).R e := algebraMap c.F _ κ' * evR Xo c f ((P j).y e he)
    have hs : ψ s = io κ' * ψ (evR Xo c f ((P j).y e he)) := by
      simp only [s, map_mul, AlgHom.commutes]; rfl
    rw [← hs]
    refine inV_of_mem_B (P j) ψ.toRingHom (fun k => ψ.commutes k) hO
      (fun g hg => (hW _).1 (hgW g hg)) s ?_
    have hyg : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    obtain ⟨d, hd'⟩ : κ j ∣ ∏ i, κ i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have e1 : ((s : (P j).R e) : (P j).Ω) = algebraMap c.F (P j).Ω (algebraMap _ c.F d) *
        (algebraMap c.F (P j).Ω (algebraMap _ c.F (κ j)) * evR Xo c f (P j).yg) := by
      rw [hyg]
      simp only [s, hκ', hd', map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_val]
      ring
    rw [e1]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨d, rfl⟩)) (hκ j)

end GlobalTheory.CuspBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetraction
section
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

noncomputable section

namespace GlobalTheory.UseLoc.ExtRet

variable {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l}

theorem algebraMap_ne_zero (LL : FinExt l) {d : ℤ_[l]} (hd : d ≠ 0) : algebraMap ℤ_[l] LL.1 d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] LL.1]
  intro h0
  apply hd
  have h1 : algebraMap ℤ_[l] ℚ_[l] d = 0 := (map_eq_zero_iff _ (algebraMap ℚ_[l] LL.1).injective).1 h0
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h1

theorem exists_mul (LL : FinExt l) (x : LL.1) : ∃ d : ℤ_[l], d ≠ 0 ∧ IsIntegral ℤ_[l] (d • x) := by
  haveI := LL.2
  haveI : Algebra.IsAlgebraic ℤ_[l] LL.1 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := LL.1)).2 inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic x).exists_integral_multiple

theorem r_smul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (c : ℤ_[l]) (z : ↥(OL LL')) :
    ((r (c • z) : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 c * ((r z : ↥(OL LL)) : LL.1) := by
  have e : c • z = incO h (algebraMap ℤ_[l] (OL LL) c) * z := by
    apply Subtype.ext
    simp [incO, Algebra.smul_def]
  rw [e, hr]
  simp

def ext (r : ↥(OL LL') →+ ↥(OL LL)) (x : LL'.1) : LL.1 :=
  ((r ⟨(exists_mul LL' x).choose • x, (exists_mul LL' x).choose_spec.2⟩ : ↥(OL LL)) : LL.1) /
    algebraMap ℤ_[l] LL.1 (exists_mul LL' x).choose

theorem ext_eq (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x)
    (x : LL'.1) (d : ℤ_[l]) (hd : d ≠ 0) (y : ↥(OL LL')) (hy : (y : LL'.1) = d • x) :
    ext r x = ((r y : ↥(OL LL)) : LL.1) / algebraMap ℤ_[l] LL.1 d := by
  unfold ext
  set d0 := (exists_mul LL' x).choose with hd0def
  have hd0 : d0 ≠ 0 := (exists_mul LL' x).choose_spec.1
  set y0 : ↥(OL LL') := ⟨d0 • x, (exists_mul LL' x).choose_spec.2⟩ with hy0
  have key : d • y0 = d0 • y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, hy0, hy, smul_smul, mul_comm]
  have k2 := congrArg (fun z => ((r z : ↥(OL LL)) : LL.1)) key
  simp only [r_smul h r hr] at k2
  rw [div_eq_div_iff (algebraMap_ne_zero LL hd0) (algebraMap_ne_zero LL hd)]
  linear_combination k2

theorem ext_add (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x₁ x₂ : LL'.1) :
    ext r (x₁ + x₂) = ext r x₁ + ext r x₂ := by
  obtain ⟨d₁, hd₁, hi₁⟩ := exists_mul LL' x₁
  obtain ⟨d₂, hd₂, hi₂⟩ := exists_mul LL' x₂
  let y₁ : ↥(OL LL') := ⟨d₁ • x₁, hi₁⟩
  let y₂ : ↥(OL LL') := ⟨d₂ • x₂, hi₂⟩
  have hy : ((d₂ • y₁ + d₁ • y₂ : ↥(OL LL')) : LL'.1) = (d₁ * d₂) • (x₁ + x₂) := by
    simp only [y₁, y₂, Subalgebra.coe_add, SetLike.val_smul, smul_smul, smul_add]
    rw [mul_comm d₂ d₁]
  rw [ext_eq h r hr _ (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hy, ext_eq h r hr x₁ d₁ hd₁ y₁ rfl,
    ext_eq h r hr x₂ d₂ hd₂ y₂ rfl, map_add, Subalgebra.coe_add, r_smul h r hr, r_smul h r hr, map_mul]
  have n₁ := algebraMap_ne_zero LL hd₁
  have n₂ := algebraMap_ne_zero LL hd₂
  field_simp

theorem ext_mul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (a : LL.1) (x : LL'.1) :
    ext r (IntermediateField.inclusion h a * x) = a * ext r x := by
  obtain ⟨d, hd, hi⟩ := exists_mul LL' x
  obtain ⟨e, he, hie⟩ := exists_mul LL a
  let y : ↥(OL LL') := ⟨d • x, hi⟩
  let a'' : ↥(OL LL) := ⟨e • a, hie⟩
  have hy : ((incO h a'' * y : ↥(OL LL')) : LL'.1) = (e * d) • (IntermediateField.inclusion h a * x) := by
    simp only [incO, y, a'', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
      SetLike.val_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    have hc : IntermediateField.inclusion h (algebraMap ℤ_[l] LL.1 e) = algebraMap ℤ_[l] LL'.1 e := by simp
    rw [hc]
    ring
  rw [ext_eq h r hr _ (e * d) (mul_ne_zero he hd) _ hy, ext_eq h r hr x d hd y rfl, hr,
    Subalgebra.coe_mul, map_mul]
  have n₁ := algebraMap_ne_zero LL hd
  have n₂ := algebraMap_ne_zero LL he
  have ha : ((a'' : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 e * a := by
    simp [a'', Algebra.smul_def]
  rw [ha]
  field_simp

theorem ext_int (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x : ↥(OL LL')) :
    ext r (x : LL'.1) = ((r x : ↥(OL LL)) : LL.1) := by
  rw [ext_eq h r hr _ 1 one_ne_zero x (by simp)]
  simp

end GlobalTheory.UseLoc.ExtRet

namespace GlobalTheory.UseLoc

theorem extRet_exists : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  intro l _ LL LL' h r hr _
  refine ⟨{ toFun := ExtRet.ext r
            map_add' := ExtRet.ext_add h r hr
            map_smul' := fun q x => ?_ }, ExtRet.ext_mul h r hr, ExtRet.ext_int h r hr⟩
  have e : q • x = IntermediateField.inclusion h (algebraMap ℚ_[l] LL.1 q) * x := by
    rw [Algebra.smul_def]
    rfl
  simp only [RingHom.id_apply]
  rw [e, ExtRet.ext_mul h r hr, Algebra.smul_def]

end GlobalTheory.UseLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOne
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem finiteDimensional_Ks_one {l : ℕ} [Fact l.Prime] (K : FinExt l) (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : K0 K = K.1 := inf_eq_left.mpr hK
  have hK1 : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin : ({x : Om l | x ^ (l ^ 1) = 1}).Finite := by
    apply ((Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (pow_pos hl 1)).2 hx
  haveI : Finite ({x : Om l | x ^ (l ^ 1) = 1}) := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    refine ⟨Polynomial.X ^ (l ^ 1) - 1, Polynomial.monic_X_pow_sub_C 1 (pow_pos hl 1).ne', ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    simp only [pow_one] at hx
    simp [hx]
  unfold Ks
  rw [h0]
  infer_instance

theorem exists_caseA_enl : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q →
    D.nd.l i ≠ D.host.d → ∃ C : TruncatedSeriesCountingIdentities.CoefExt D i w hw, CaseA (D.nbr i w hw).Kw C.LL := by
  intro D i w hw hs hq hd
  have h2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hs
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i hs hq hd w hw
  haveI := finiteDimensional_Ks_one (D.nbr i w hw).Kw hur
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).LL.1 := (D.nbr i w hw).LL.2
  let N : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    IntermediateField.normalClosure ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) (Om (D.nd.l i))
  haveI hN : FiniteDimensional ℚ_[D.nd.l i] ↥N := normalClosure.is_finiteDimensional _ _ _
  let LL : FinExt (D.nd.l i) := ⟨N ⊔ (D.nbr i w hw).LL.1, inferInstance⟩
  refine ⟨⟨LL, le_sup_right⟩, hur, h2, le_rfl, fun h => absurd h h2, ?_, ?_⟩
  · have h0 : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hur
    unfold Ks
    rw [h0]
    exact le_sup_left
  · intro τ x
    apply le_sup_left (b := (D.nbr i w hw).LL.1)
    exact AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩

end GlobalTheory.UseLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnitStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  first | exact @GlobalTheory.CutCoreUnit.main | exact GlobalTheory.CutCoreUnit.main | (intros; apply GlobalTheory.CutCoreUnit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalarStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_component_readings_unit_modulus_scalar : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  first | exact @GlobalTheory.CoverFrameMod.comp_over_comp_norm | exact GlobalTheory.CoverFrameMod.comp_over_comp_norm | (intros; apply GlobalTheory.CoverFrameMod.comp_over_comp_norm <;> assumption)
end

