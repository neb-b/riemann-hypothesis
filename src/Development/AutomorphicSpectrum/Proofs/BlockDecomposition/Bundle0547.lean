module

public import Mathlib
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff
section
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors NNReal

namespace GlobalTheory.CompanionTheory.PartialZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F] {χ : HeckeCharacter F}

theorem conductor_eq_top (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have hd : χ.conductor ∣ ⊤ := by
    refine (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine h ((mem_standardOpenSubgroup_iff_toFinite_mem _).2 ?_)
    rw [toFinite_ofFinite]
    have hx' : x ∈ idealLevel (⊤ : Ideal (𝓞 F)) := hx
    rw [idealLevel, mem_finiteLevel] at hx'
    rw [mem_finiteLevel]
    intro v
    have hv := hx' v
    have h0 : multiplicity v.asIdeal (⊤ : Ideal (𝓞 F)) = 0 :=
      multiplicity_eq_zero_of_not_dvd fun hdv ↦ v.isPrime.ne_top (by
        rwa [Ideal.dvd_iff_le, top_le_iff] at hdv)
    rw [h0] at hv
    exact hv
  rwa [Ideal.dvd_iff_le, top_le_iff] at hd

theorem infiniteWeight_eq_zero (h : standardOpenSubgroup F ≤ χ.toIdele.ker)
    (w : InfinitePlace F) : χ.infiniteWeight w = 0 := by
  have hp : χ.infiniteParams w = (0, 0) := by
    refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
    have h1 : χ.infiniteComponent w a = 1 := h (infiniteEmbedding_mem_standardOpenSubgroup w a)
    simp [h1]
  rw [HeckeCharacter.infiniteWeight, hp]

theorem idealUnit_eq_one {I : Ideal (𝓞 F)} (hI : I = ⊤) (h : I ≠ ⊥) : idealUnit I h = 1 := by
  subst hI
  ext
  simp [idealUnit]

theorem finiteFourier_eq (h : χ.conductor = ⊤) {δ : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    finiteFourier F χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) := by
  have hE : IsEmpty χ.conductorPrimes := ⟨fun v ↦ by
    have hv := χ.mem_conductorPrimes.1 v.2
    rw [h, Ideal.dvd_iff_le, top_le_iff] at hv
    exact v.1.isPrime.ne_top hv⟩
  rw [χ.finiteFourier_finiteTestFun_inv_eq hδ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]

theorem discr_sqrt_mul (h : χ.conductor = ⊤) :
    (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) * (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  have hd : χ.discrNormConductor = |(discr F : ℝ)| := by
    rw [HeckeCharacter.discrNormConductor, h, Ideal.absNorm_top]
    simp
  have hpos : 0 < |(discr F : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hs : ((NNReal.sqrt ‖discr F‖₊ : ℝ≥0) : ℝ) = Real.sqrt |(discr F : ℝ)| := by
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hcp : ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos.le]
    norm_num
  have hne : ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
  have hinv : (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)⁻¹ := by
    rw [← hs]
    simp
  rw [hd, hcp, hinv, inv_mul_cancel₀ hne]

theorem rootNumber_eq_coeff_different (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)) := by
  have hc := conductor_eq_top h
  have hδ := χ.toFractionalIdeal_conductorDifferentIdele
  have hcop : IsCoprime (differentIdeal ℤ (𝓞 F)) χ.conductor := by
    rw [hc, ← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hmem : ofFinite χ.conductorDifferentIdele ∈ primeToLevel χ.conductor := by
    refine mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩
    rw [hc, Ideal.dvd_iff_le, top_le_iff] at hv
    exact absurd hv v.isPrime.ne_top
  have hval : χ.coeff (differentIdeal ℤ (𝓞 F)) =
      (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) := by
    rw [χ.coeff_of_mem ⟨differentIdeal_ne_bot, hcop⟩]
    congr 1
    refine χ.idealCharacter_apply hmem _ ?_
    rw [hδ, idealUnit_eq_one hc, one_mul]
    rfl
  rw [hval, HeckeCharacter.rootNumber, HeckeCharacter.fourierConst, finiteFourier_eq hc hδ]
  simp only [infiniteWeight_eq_zero h, Int.natAbs_zero, pow_zero, Finset.prod_const_one, one_mul]
  linear_combination (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * discr_sqrt_mul hc

end

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzArchContinuousIntegrable
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple

theorem decay_of_functionals {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [Fintype ι] {N : ℕ}
    (e : V ≃+ (Fin N → ℝ)) (hes : Continuous e.symm) (c : ι → V →+ ℂ) (hc : ∀ i, Continuous (c i))
    (f : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X : V, (∃ i, R < ‖c i X‖) → ‖f (e X)‖ ≤ C / R ^ k := by
  let L : ι → (Fin N → ℝ) →L[ℝ] ℂ := fun i =>
    ((c i).comp e.symm.toAddMonoidHom).toRealLinearMap ((hc i).comp hes)
  have hL : ∀ i X, c i X = L i (e X) := by
    intro i X
    show c i X = c i (e.symm (e X))
    rw [e.symm_apply_apply]
  set T : ℝ := ∑ i, ‖L i‖ + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ ∑ i, ‖L i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨C0, hC0⟩ := f.decay k 0
  refine ⟨C0 * T ^ k, fun R hR X ⟨i, hi⟩ => ?_⟩
  have hRpos : 0 < R := by linarith
  set x := e X with hx
  have hb : ‖c i X‖ ≤ T * ‖x‖ := by
    rw [hL]
    refine ((L i).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have : ‖L i‖ ≤ ∑ j, ‖L j‖ :=
      Finset.single_le_sum (f := fun j => ‖L j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  have hRx : R ≤ T * ‖x‖ := hi.le.trans hb
  have hd : ‖x‖ ^ k * ‖f x‖ ≤ C0 := by
    simpa [norm_iteratedFDeriv_zero] using hC0.2 x
  rw [le_div_iff₀ (pow_pos hRpos k)]
  calc ‖f x‖ * R ^ k ≤ ‖f x‖ * (T * ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRpos.le hRx k) (norm_nonneg _)
    _ = (‖x‖ ^ k * ‖f x‖) * T ^ k := by rw [mul_pow]; ring
    _ ≤ C0 * T ^ k := mul_le_mul_of_nonneg_right hd (pow_nonneg hTpos.le k)

theorem schwartzArch_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)), IsHomeomorph κ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Continuous φ ∧ Integrable φ (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) ∧ (∃ B : ℝ, ∀ X, ‖φ X‖ ≤ B) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k := by
  intro F E _ _ _ _ _ σ hCM κ hκ n M d b lam hlam φ hφ
  have hloc := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, hsc, -, hrepr, hB, -, hgc⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := hB n M
  obtain ⟨-, hW, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b lam hlam
  haveI := hW n M
  obtain ⟨N, e, he, hes, f, hf⟩ := hφ
  have hφe : φ = fun x => f (e x) := funext hf
  have hφc : Continuous φ := by rw [hφe]; exact f.continuous.comp he
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμ
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hint : Integrable φ μ := by
    have h1 : Integrable (fun x => f x) (μ.map e) := f.integrable
    rw [hφe]
    exact (integrable_map_measure h1.aestronglyMeasurable he.measurable.aemeasurable).1 h1
  refine ⟨hφc, hint, ?_, fun k => ?_⟩
  · obtain ⟨C0, hC0⟩ := f.decay 0 0
    refine ⟨C0, fun X => ?_⟩
    rw [hf]
    simpa [norm_iteratedFDeriv_zero] using hC0.2 (e X)
  · let c : (Fin n × Fin M × NumberField.InfinitePlace F) → (Fin n → Fin M → Ainf F ⊗[F] E) →+ ℂ := fun p =>
      { toFun := fun X => κ (X p.1 p.2.1) p.2.2
        map_zero' := by simp
        map_add' := fun X Y => by simp }
    have hc : ∀ p, Continuous (c p) := fun p =>
      (continuous_apply p.2.2).comp (hκ.continuous.comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1)))
    obtain ⟨C, hC⟩ := decay_of_functionals e hes c hc f k
    refine ⟨C, fun R hR X hX => ?_⟩
    rw [hf]
    refine hC R hR X ?_
    simp only [boxK, Set.mem_setOf_eq, not_forall, not_le] at hX
    obtain ⟨a, i, w, h⟩ := hX
    exact ⟨(a, i, w), h⟩

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProducts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem schwartzBruhat_eq_sum_pureTuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨k, Φinf, Φf, hinf, hf, hsum⟩ := hΦ
  choose s A S hA hAS hdec using fun i => GlobalTheory.CompanionTheory.WhitFree.DecN.exists_box_combN b (Φf i) (hf i)
  let e := Fintype.equivFin (Σ i : Fin k, (s i))
  refine ⟨Fintype.card (Σ i : Fin k, (s i)),
    fun j Z => Φinf (e.symm j).1 Z * Φf (e.symm j).1 (e.symm j).2,
    fun j => A (e.symm j).1 (e.symm j).2, Finset.univ.biUnion S, ?_, ?_, ?_, ?_⟩
  · intro j
    exact GlobalTheory.CompanionTheory.WhitFree.DecN.isSchwartzArch_const_mulN (hinf _) _
  · intro j v
    exact hA _ _ v
  · intro j v hv
    exact hAS _ _ (e.symm j).2.2 v
      (fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  · intro X
    rw [hsum X]
    symm
    refine (Equiv.sum_comp e.symm (fun p : (Σ i : Fin k, (s i)) =>
      pureN (fun Z => Φinf p.1 Z * Φf p.1 p.2) (A p.1 p.2) X)).trans ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
    exact mul_assoc _ _ _

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.SchGlue

open GlobalTheory.Published.SiegelOneVector

variable {D : D7}

theorem exists_homeomorph_of_sections {A Y Z : Type} [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : A → Y) (s : Y → A) (c : Y → Z) (σ : Z → A) (hp : Continuous p) (hs : Continuous s)
    (hc : Continuous fun a => c (p a)) (hσ : Continuous σ) (h1 : ∀ y, p (s y) = y)
    (h2 : ∀ z, c (p (σ z)) = z) (h3 : ∀ y, p (σ (c y)) = y) :
    ∃ P : Y ≃ₜ Z, ∀ y, P y = c y := by
  have hcc : Continuous c := by
    have : c = (fun a => c (p a)) ∘ s := funext fun y => by simp only [Function.comp, h1]
    rw [this]
    exact hc.comp hs
  exact ⟨{ toFun := c, invFun := fun z => p (σ z), left_inv := h3, right_inv := h2,
           continuous_toFun := hcc, continuous_invFun := hp.comp hσ }, fun _ => rfl⟩


set_option maxHeartbeats 1600000 in
theorem exists_infHomeo {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ P : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → ℂ), ∀ y τ, P y τ = θ τ y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, hec, hec'⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ y, infPart D (e.symm (y, 0)) = y := fun y => by
    have := (he (e.symm (y, 0))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hfin : ∀ y, finPart D (e.symm (y, 0)) = 0 := fun y => by
    have := (he (e.symm (y, 0))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hci : Continuous (infPart D) := by
    have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => ((he z).1).symm
    rw [this]
    exact continuous_fst.comp hec
  have hs : Continuous fun y : Ainf D.host.F ⊗[D.host.F] D.host.E => e.symm (y, 0) :=
    hec'.comp (continuous_id.prodMk continuous_const)
  have hback : ∀ a : AE D, finPart D a = 0 → a = σ fun τ => θ τ (infPart D a) := fun a ha => by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, hσ.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, hσ.comp, sub_self]
  obtain ⟨P, hP⟩ := exists_homeomorph_of_sections (infPart D : AE D → _) (fun y => e.symm (y, 0))
    (fun (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) => θ τ y) σ hci hs
    (continuous_pi fun τ => GlobalTheory.FockCompare.continuous_comp hθ τ) hσ.cont hinf
    (fun z => funext fun τ => hσ.comp z τ)
    (fun y => by
      obtain ⟨a, ha⟩ : ∃ a : AE D, a = e.symm (y, 0) := ⟨_, rfl⟩
      have h1 : infPart D a = y := ha ▸ hinf y
      have h2 : finPart D a = 0 := ha ▸ hfin y
      subst h1
      exact congrArg (infPart D) (hback a h2).symm)
  exact ⟨P, fun y τ => congrFun (hP y) τ⟩

theorem isSchwartzArch_comp {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    (f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) (M := m) (n := r)
      fun Y => f fun τ i j => θ τ (Y j i) := by
  obtain ⟨P, hP⟩ := exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add (f := _)]
  let B : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)) → ℝ) :=
    (Module.finBasis ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)).equivFun.toContinuousLinearEquiv
  refine ⟨_, (AddEquiv.mk' Q.toEquiv hadd).trans B.toLinearEquiv.toAddEquiv,
    B.continuous.comp Q.continuous, Q.symm.continuous.comp B.symm.continuous,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B.symm f, fun Y => ?_⟩
  show _ = f (B.symm (B (Q Y)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg f (funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm)

theorem isSB_swap {m r : ℕ} {g : (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSB fun Y : Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E => g fun i j => Y j i := by
  let S : (Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun Y i j => Y j i
      invFun := fun Y j i => Y i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  exact ⟨hg.1.comp_continuous S.continuous, hg.2.comp_homeomorph S⟩

theorem isSchwartzArch_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (h : IsSchwartzArch (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) fun X => c * Φ X := by
  obtain ⟨N, e, h1, h2, f, hf⟩ := h
  exact ⟨N, e, h1, h2, c • f, fun X => by simp [hf]⟩

theorem sb_zero {M n : ℕ} :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (0 : (Fin n → Fin M → AE D) → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp⟩

theorem sb_add {M n : ℕ} {Φ Ψ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ)
    (hΨ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Ψ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (Φ + Ψ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  obtain ⟨k', a', b', ha', hb', hs'⟩ := hΨ
  refine ⟨k + k', Fin.append a a', Fin.append b b', fun i => ?_, fun i => ?_, fun X => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ha i
    · rw [Fin.append_right]; exact ha' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add, Pi.add_apply, hs, hs']
    simp only [Fin.append_left, Fin.append_right]

theorem sb_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (c • Φ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  refine ⟨k, fun i X => c * a i X, b, fun i => isSchwartzArch_smul c (ha i), hb, fun X => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.SiegelND.SchGlue

namespace GlobalTheory.CompanionTheory.SiegelND

open GlobalTheory.CompanionTheory.SiegelND.SchGlue

theorem isSchwartzBruhat_tupOf_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  intro D θ hθ m r φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨1, fun _ Y => f fun τ i j => θ τ (Y j i), fun _ Y => g fun i j => Y j i,
      fun _ => isSchwartzArch_comp hθ f, fun _ => isSB_swap hg, fun X => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | zero => exact sb_zero
  | add a b _ _ ha hb => exact sb_add ha hb
  | smul c a _ ha => exact sb_smul c ha

end GlobalTheory.CompanionTheory.SiegelND
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.NormSplit

theorem thetaGL_eq_id_map {R : Type} [CommRing R] (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    thetaGL a c g = thetaGL a (RingHom.id _) (GeneralLinearGroup.map c g) := by
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv]
  rfl

theorem ratW_mul_thetaGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
    ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := by
  intro E _ _ _ n w δ hs
  unfold locEl
  rw [if_pos hs, map_mul]
  congr 1
  unfold thE
  rw [thetaGL_eq_id_map n (IsCMField.complexConj E).toRingEquiv.toRingHom δ]
  exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) (RingHom.id _) (RingHom.id _) (fun _ => rfl) _).symm

end GlobalTheory.CompanionTheory.NormSplit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardOpenSubgroupLeKerInv
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem standardOpenSubgroup_le_ker_inv (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    standardOpenSubgroup F ≤ (χ⁻¹).toIdele.ker := by
  intro x hx
  have hx' : χ.toIdele x = 1 := h hx
  show (χ⁻¹).toIdele x = 1
  rw [HeckeCharacter.toIdele_apply] at hx' ⊢
  change (χ _)⁻¹ = 1
  rw [hx', inv_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

