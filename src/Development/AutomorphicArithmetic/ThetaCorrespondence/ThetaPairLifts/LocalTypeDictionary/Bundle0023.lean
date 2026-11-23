module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LinearFunctionalSphericalVectorNeZero
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.VacLinW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem linearFunctional_sphericalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.T.splitPlace_linearFunctional_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v t b c
  have hcm : IsCMExt F E σ := hPair.base.cm
  obtain ⟨hSB, hne, θ, -, hfix⟩ := hPair.good.vac v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have htt : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hfix' : ∀ γ ∈ latAtV X W v, (γ.map (piW (t.comp σ)) = 0 ∨ γ.map (piW t) = 0) →
      Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v) (M.vac v) := by
    intro γ hγ h
    have h0 : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ = 0 := by
      rcases h with h | h
      · exact symp_eq_zero_of_comp hcm t (hat γ hγ) h h _ _ _
      · rw [← htt] at h
        exact symp_eq_zero_of_comp hcm (t.comp σ) (hat γ hγ) h h _ _ _
    have := hfix γ hγ
    rwa [h0, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  set f := ι (M.vac v) with hf
  set S : Set (Matrix (Fin n) (Fin d) (Fv F v)) := {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} with hS
  have htr : ∀ A ∈ S, ∀ Y, f (Y + A) = f Y := by
    intro A hA Y
    obtain ⟨γ, hγ, h0, hco⟩ := GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate hcm X W v t b c hb hc A hA
    have := hι.trans γ (hat γ hγ) h0 _ hSB _ hSB (hfix' γ hγ (Or.inl h0)) Y
    rw [hco] at this
    exact this.symm
  have hsupp : ∀ Y, f Y ≠ 0 → Y ∈ S := by
    intro Y hY
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq hcm v t b c Y
    have hψ : ∀ u ∈ latAtV X W v, u.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1 := by
      intro u hu hu0
      have hm := hι.mult u (hat u hu) hu0 _ hSB _ hSB (hfix' u hu (Or.inr hu0)) x hx hx0
      exact (mul_eq_right₀ hY).mp hm.symm
    have hmem : x ∈ latAtV X W v := by
      refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hPair.base hPair.herm hPair.skew v x hx).2
        fun γ hγ => ?_
      obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl, h₁, h₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hcm X W v t γ hγ
      rw [symp_add_right, symp_eq_zero_of_comp hcm t hx hx0 h₁, zero_add]
      exact hψ γ₂ hγ₂ h₂
    exact GlobalTheory.T.splitPlace_tensorLattice_component_integral X W v t b c hb hc x hmem
  have hf0 : f ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn hSB (zero_mem _) ?_
    rw [map_zero]; exact h
  have hfe : f = f 0 • S.indicator 1 := by
    funext Y
    by_cases hY : Y ∈ S
    · rw [Pi.smul_apply, Set.indicator_of_mem hY, Pi.one_apply, smul_eq_mul, mul_one, ← htr Y hY 0, zero_add]
    · rw [Pi.smul_apply, Set.indicator_of_notMem hY, smul_zero]
      by_contra h
      exact hY (hsupp Y h)
  have hz : f 0 ≠ 0 := by
    intro h
    apply hf0
    rw [hfe, h, zero_smul]
  refine ⟨(f 0)⁻¹ • ι, isLin_smul M B.ψ hι (inv_ne_zero hz), ?_⟩
  rw [LinearMap.smul_apply, ← hf]
  exact (congrArg ((f 0)⁻¹ • ·) hfe).trans (by rw [smul_smul, inv_mul_cancel₀ hz, one_smul])
end GlobalTheory.VacLinW
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearFunctional_sphericalVector_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @_root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector | exact _root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector | (intros; apply _root_.GlobalTheory.VacLinW.linearFunctional_sphericalVector <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MetaplecticScalarDerivativeNonempty
section
section
open scoped Matrix
noncomputable section
namespace GlobalTheory.MetaplecticScalarDeriv
open MeasureTheory Filter Topology GlobalTheory.RealWeil
theorem metaplectic_scalar_derivative_nonempty (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l] [Nonempty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hZ : Z ∈ LieAlgebra.Symplectic.sp l ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTrho : ∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h →
      ⇑(T t h₁) = rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h))
    (hTiso : ∀ (t : ℝ) (h : Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩ := hP.realMetaplecticRepresentation l
  obtain ⟨γ, -, hγ0, hγadd, hγpr, hγd⟩ := h6 Z hZ
  have hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f := by
    intro s t f
    rw [hγadd, map_mul]
    rfl
  have hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f := by
    intro t f
    rw [hmul, neg_add_cancel, hγ0, map_one]
    rfl
  have hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f := by
    intro t f
    rw [hmul, add_neg_cancel, hγ0, map_one]
    rfl
  have hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
    intro t w
    have e : pr (γ t) * pr (γ (-t)) = 1 := by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]
    have e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
      congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
    rw [← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
  have hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h := by
    intro t
    refine _root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]
  choose ν _hνn hν using hU
  have hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f := by
    intro t f
    have := hν t (omS (γ t) f)
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1] using this
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hν0 : ν 0 = 1 := by
    have e := congrArg (fun g : Sch l => g 0) (hTν 0 f0)
    simp only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e
    change 1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e
    rw [ContinuousLinearMap.one_apply, hf0, mul_one] at e
    exact e.symm
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    set f := omS (γ (-(s + t))) f0
    have e1 : T (s + t) f = ν (s + t) • f0 := by rw [hTν, hS2]
    have e2 : T (s + t) f = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]
    have e := congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)
    simpa [hf0] using e
  have hcontS : ContinuousAt (fun t => omS (γ t) f0) 0 := by
    have hd := _root_.GlobalTheory.RealWeil.tendsto_slope_omS_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0) := by
      have h1' := h1.add_const f0
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]
    exact h2
  have hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0 := (continuous_eval l 0).continuousAt.comp hcontS
  have hS00 : omS (γ 0) f0 0 ≠ 0 := by
    rw [hγ0, map_one, ContinuousLinearMap.one_apply, hf0]
    exact one_ne_zero
  have hνc : ContinuousAt ν 0 := by
    have hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0 :=
      (hTcont f0 0).continuousAt.div hcontS0 hS00
    refine hq.congr ?_
    filter_upwards [hcontS0.eventually_ne hS00] with t ht
    rw [hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul ν hν0 hνmul hνc
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hd := _root_.GlobalTheory.RealWeil.tendsto_slope_omS_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    rw [← hν0]
    exact hνc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hν1.smul hd).add (hslope.smul_const f)
  rw [one_smul, add_comm] at hlim
  refine hlim.congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  intro hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont
  rcases isEmpty_or_nonempty l with hl | hl
  · exact main_empty l Z T hT0 hTadd hTcont
  · exact _root_.GlobalTheory.MetaplecticScalarDeriv.metaplectic_scalar_derivative_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont
end GlobalTheory.MetaplecticScalarDeriv
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  first | exact @_root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | exact _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MetaplecticSplittingUniqueUpToCharacter
section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
noncomputable section
namespace GlobalTheory.SplitScalar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem metaplectic_splittings_differ_by_character : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  intro hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont
  have key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
      ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ := by
    intro g
    by_cases hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)
    swap
    · exact ⟨1, fun h => absurd h hg⟩
    have hgi := at_inv hg
    have hscalar : ∃ z : ℂ, ∀ φ ∈ schA F κ, (om g * ω₀ g⁻¹) φ = z • φ :=
      _root_.GlobalTheory.T.adelic_intertwiner_eq_scalar hP F κ ψ hψ (om g * ω₀ g⁻¹)
      (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ))
      (fun w φ hφ => by
        have e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ := by simp [Darboux.rho]
        rw [Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ,
          hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]
        simp [Darboux.rho])
      (fun μ hμ φ hφ => by
        rw [Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])
    obtain ⟨z, hz⟩ := hscalar
    refine ⟨z, fun _ φ hφ => ?_⟩
    have := hz (ω₀ g φ) ((hω g hg).1 φ hφ)
    rwa [Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  choose z hz using key
  by_cases h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0
  swap
  · push_neg at h0
    refine ⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩
    rw [h0 φ hφ, map_zero, map_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  refine ⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩
  · have hgh := at_mul hg hh
    apply smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)
    show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀
    rw [← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul,
      hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (apply_ne_zero ω₀ g hne)
    have hl := proj_mem_adm F κ x
    have c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g := hcont _ hl φ₀ hφ₀ g hg
    have c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g :=
      (hom.cont _ hl φ₀ hφ₀).continuousWithinAt
    have hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0 := hx
    have c3 := c2.div c1 hx'
    have hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) →
        (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 →
        z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) /
          (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) := by
      intro q hqS hq0
      rw [hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]
    refine c3.congr_of_eventuallyEq ?_ (hq g hg hx')
    filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS
    exact hq q hqS hq0
  · have := hz g hg φ₀ hφ₀
    rw [h0, zero_smul] at this
    exact apply_ne_zero om g hne this
end GlobalTheory.SplitScalar
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplectic_splitting_unique_up_to_character : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @_root_.GlobalTheory.SplitScalar.metaplectic_splittings_differ_by_character | exact _root_.GlobalTheory.SplitScalar.metaplectic_splittings_differ_by_character | (intros; apply _root_.GlobalTheory.SplitScalar.metaplectic_splittings_differ_by_character <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumIsVacuumIntegral
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict
theorem moved_vacuum_isVacuumIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  have hn := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  set gh := ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
    ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) with hgh
  have mem : gh.1 ∈ GfC (ch.G.pS p) ∧ gh.2 ∈ GfC (ch.G.pT p) := by
    rw [hgh]
    cases p with
    | chi i j => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | mu t i j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
    | core i => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | top t j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
  obtain ⟨hstd, hv⟩ := ch.S.Z.vac_is p hp
  have hact := (_root_.GlobalTheory.T.twisted_moved_lattice_action hPr hInp ch hIs p hp x y).2
  have hth' := hom.om_pres gh _ hv.theta
  have hgh' : gh = (gh.1, gh.2) := rfl
  refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩, fock := fun τ z => ?_, norm := ⟨hv.norm.1, fun q hq => ?_⟩ }⟩
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    have h2 : actO _ _ gh.1 gh.2 u + actO _ _ gh.1 gh.2 u = actO _ _ gh.1 gh.2 (u + u) := by
      simp only [actO, Matrix.mul_add, Matrix.add_mul]
    have h3 := hv.lat.1 u hu
    rw [two_nsmul] at h3 ⊢
    rw [h2, hgh', ← hom.om_heis gh.1 gh.2 _ _ hv.theta, h3]
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    rw [hgh', ← hom.om_heis gh.1 gh.2 u _ hv.theta, hv.lat.2 e he u hu (GlobalTheory.MovedVac.halfBack D _ _ gh.1 gh.2 e u hhalf)]
  · have hθ := ch.W.θ_is
    have e : ∀ z', Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.W.om p gh (ch.S.Z.vac p)) =
        ch.W.om p gh (Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.S.Z.vac p)) := by
      intro z'
      rw [hgh', GlobalTheory.OrientedHeis.om_dRho hom hθ gh.1 gh.2 τ z' hv.theta, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ mem.2,
        GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ (inv_mem mem.1), Matrix.one_mul, Matrix.mul_one]
    have h0 := hv.fock τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
  · show nrm2 q.1 q.2 (ch.W.om p gh (ch.S.Z.vac p)) = 1
    have hU := hom.om_unit q.1 q.2 hq.1 hq.2.1 gh _ hv.theta
    haveI : OpensMeasurableSpace (WO (ch.G.pS p) (ch.G.pT p)) := ⟨le_rfl⟩
    have key : ∀ F : WO (ch.G.pS p) (ch.G.pT p) → ℂ, Continuous F → nrm2 q.1 q.2 F = (∫⁻ w in q.2, ‖F w‖ₑ ^ 2 ∂q.1).toReal := by
      intro F hF
      unfold nrm2
      have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
        (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
      congr 1
      refine MeasureTheory.lintegral_congr fun w => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [key _ hth'.cont, hU, ← key _ hv.theta.cont]
    exact hv.norm.2 q hq
end GlobalTheory.MovedDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_moved_vacuum_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | exact _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral <;> assumption)
end
end

