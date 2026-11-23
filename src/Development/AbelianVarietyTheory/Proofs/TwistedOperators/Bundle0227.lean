module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactActionPreservesPolynomialDegree
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.LeftHaar

def transposeCAE (D : D7) (m n : ℕ) : Mx D m n ≃ₜ+ Mx D n m where
  toAddEquiv := Matrix.transposeAddEquiv (Fin m) (Fin n) (AE D)
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem map_left_unitary (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r))
    (hν : ν.IsAddHaarMeasure) :
    ν.map (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) = ν := by
  have hJ : IsHermND D.sp.cm.sig W.gram := GlobalTheory.Mem.VolExists.isHermND D.sp.cm W
  obtain ⟨g', hg'⟩ := GlobalTheory.AdelicModulus.Row.exists_transpose (AF D.host.F) hJ h
  have hK := GlobalTheory.AdelicModulus.Row.isHermND_inv_transpose hJ
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r W.rank) := ⟨rfl⟩
  let T := transposeCAE D W.rank r
  have hT : Measurable T := T.continuous.measurable
  have hTs : Measurable T.symm := T.symm.continuous.measurable
  haveI hμ' : (ν.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map ν
  have hm := GlobalTheory.mul_unitary_map_haar D W.rank r (W.gram⁻¹)ᵀ hK.1 hK.2 g' (ν.map T) hμ'
  set A : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig (W.gram⁻¹)ᵀ g').1
  have hR : Measurable (fun x : Mx D r W.rank =>
      (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hmt : mt W h = (HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1 := rfl
  have hf : (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) =
      T.symm ∘ (fun x : Mx D r W.rank => (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) ∘ T := by
    funext y
    simp only [Function.comp_apply, A, hg', hmt]
    show _ = ((y : Matrix (Fin W.rank) (Fin r) (AE D))ᵀ * ((HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1)ᵀ)ᵀ
    rw [← Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hf, ← Measure.map_map hTs (hR.comp hT), ← Measure.map_map hR hT, hm, Measure.map_map hTs hT]
  have : (T.symm ∘ T : Mx D W.rank r → Mx D W.rank r) = id := by
    funext y; simp
  rw [this, Measure.map_id]

theorem integral_left_unitary : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)),
    ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ,
    ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν =
      ∫ y, Φ y ∂ν := by
  intro D W r h ν hν Φ
  let u := HA.mat (AF D.host.F) D.sp.cm.sig W.gram h
  have hmt : mt W h = u.1 := rfl
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  let e : Mx D W.rank r ≃ᵐ Mx D W.rank r :=
    { toFun := fun y => (HMul.hMul u.1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      invFun := fun y => (HMul.hMul (u⁻¹).1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      left_inv := fun y => by
        show (u⁻¹).1 * (u.1 * y) = y
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        show u.1 * ((u⁻¹).1 * y) = y
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable }
  have hmap := map_left_unitary D W r h ν hν
  rw [hmt] at hmap
  have he : Measure.map (⇑e) ν = ν := hmap
  have := integral_map_equiv (μ := ν) e Φ
  rw [he] at this
  rw [hmt]
  exact this.symm

end GlobalTheory.Twist.LeftHaar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralParametricUnfoldRationalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnfoldRat

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩)
    ⟨fun _ _ h => GlobalTheory.MixModel.rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, hξ⟩ => ⟨ξ, Subtype.ext hξ⟩⟩

theorem countable_ratMx (D : D7) (m n : ℕ) : Countable (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : DiscreteTopology (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := i5
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI := countable_ratMx D m n
  exact (ratEquiv D m n).injective.countable

theorem lintegral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℝ≥0∞) :
    ∫⁻ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.lintegral_eq_tsum'' φ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem integral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℂ) (hφ : Integrable φ μ) :
    ∫ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.integral_eq_tsum'' φ hφ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem unfold : ∀ (D : D7) (m n : ℕ) (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n)),
    IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨 → ∀ (h : X → Mx D m n → ℂ), Continuous (Function.uncurry h) →
    ∀ M : ℝ, (∀ x u, Summable (fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ M) →
    Integrable (fun u => ∫ x, h x u ∂ν) μ ∧ ∫ u, (∫ x, h x u ∂ν) ∂μ =
      ∫ t in 𝓨, (∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν) ∂μ := by
  intro D m n X _ _ _ _ ν _ μ 𝓨 hcov h hc M hM
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_mat D m n
  haveI := hcov.1
  haveI : FirstCountableTopology (Mx D m n) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hr0 : (0 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) = 0 := Matrix.map_zero _ (map_zero (incA D))

  have hb : ∀ x u, ‖h x u‖ ≤ M := fun x u => by
    have h0 := (hM x u).1.le_tsum 0 (fun _ _ => norm_nonneg _)
    rw [hr0, zero_add] at h0
    exact h0.trans (hM x u).2
  have hcx : ∀ x, Continuous (h x) := fun x => hc.comp (continuous_const.prodMk continuous_id)
  have hcu : ∀ u, Continuous fun x => h x u := fun u => hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (Function.uncurry h) := hc.measurable

  have hmx : ∀ x (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun t => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun x ξ => ((hcx x).comp ((continuous_const.add continuous_id))).measurable.enorm
  have hmu : ∀ t (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun x => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun t ξ => (hcu (ξ.map (incA D) + t)).measurable.enorm
  have hsum : ∀ x t, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ≤ ENNReal.ofReal M := fun x t => by
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hM x t).1]
    exact ENNReal.ofReal_le_ofReal (hM x t).2
  have hlx : ∀ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ≤ ENNReal.ofReal M := fun x => by
    have e1 : ∫⁻ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ :=
      lintegral_tsum fun ξ => (hmx x ξ).aemeasurable
    rw [lintegral_unfold hcov (fun u => ‖h x u‖ₑ), ← e1]
    refine (lintegral_mono fun t => hsum x t).trans ?_
    rw [setLIntegral_const, hcov.2.2, mul_one]

  have hGc : Continuous fun u => ∫ x, h x u ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun u => (hcu u).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun x => hb x u) (integrable_const M)
      (Filter.Eventually.of_forall fun x => hcx x)

  have hGi : Integrable (fun u => ∫ x, h x u ∂ν) μ := by
    refine ⟨hGc.aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ u, ‖∫ x, h x u ∂ν‖ₑ ∂μ ≤ ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ :=
      lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    have h2 : ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ = ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν :=
      lintegral_lintegral_swap (hmeas.enorm.comp measurable_swap).aemeasurable
    have h3 : ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν ≤ ENNReal.ofReal M * ν Set.univ := by
      rw [← lintegral_const]; exact lintegral_mono fun x => hlx x
    exact lt_of_le_of_lt (h1.trans (h2.le.trans h3)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  refine ⟨hGi, ?_⟩
  rw [integral_unfold hcov _ hGi]

  have hA : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖∫ x, h x (ξ.map (incA D) + t) ∂ν‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_unfold hcov (fun u => ‖∫ x, h x u ∂ν‖ₑ)]; exact hGi.2.ne
  have e3 : ∫ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ :=
    integral_tsum (fun ξ => (hGc.comp ((continuous_const.add continuous_id))).aestronglyMeasurable) hA
  rw [← e3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)

  have hB : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν ≠ ∞ := by
    have e2 : ∫⁻ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν :=
      lintegral_tsum fun ξ => (hmu t ξ).aemeasurable
    rw [← e2]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => hsum x t) ?_)
    rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have e4 : ∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν :=
    integral_tsum (fun (ξ : Matrix (Fin m) (Fin n) D.host.E) => (hcu (ξ.map (incA D) + t)).aestronglyMeasurable) hB
  exact e4.symm

end GlobalTheory.UnfoldRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem one_mem_Kset {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem isItW_of_globIt {M : DSModel V S} {M' : DSModel W S'} {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF D.host.F) ℂ} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    {aS aT : D.what₂.Tau → ℚ} {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    {I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ} (hI : GlobIt M M' aS aT It I)
    (hr : D.what₂.Tau → 0 < V.rank ∧ 0 < W.rank) (hpt : Function.Injective (ptOf ψ θ M M' f))
    (hC : ∀ τ, CompactFock ψ θ M M' ω f τ (aS τ) (aT τ)) (hL : ∀ τ, LieFock ψ θ M M' ω f τ (aS τ) (aT τ)) :
    IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  first
  | exact @_root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt
  | exact _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt
  | (apply _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt <;> assumption)
  | (intros; apply _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt ..)

theorem exists_locIt {X : ProvA} (hX : ChosenSeries X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X)
    (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ be) (ga ++ de) aT))
    (hS' : S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨-, p1, p2, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + be.length) (ga.length + de.length) _ _ aT
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + de.length + t) (ga.length + be.length) _ _ aS
    ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨Φ, hΦ⟩ := (h1.1 t al be ga de hd).1
  obtain ⟨Tm, hi, hq, -⟩ := h2.1 t al be ga de hd Φ hΦ
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.Chain.CoverContr.exists_isCoverIt _ _ _ _ _ _ _ _ _ _ Tm hi hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨v, hv, -⟩ := (hX _ _ _ p2).1
  have c1 := Fintype.card_congr e
  have c2 := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_fin] at c1 c2
  exact ⟨⟨by omega, by omega⟩,
    GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ B hm hm' hU hU' ⟨v, 0, hv⟩ hκ hB⟩

theorem itPair (D : D7) (X : ProvA) (hX : ChosenSeries X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : VacChar D) (hB : ModelsAreCoverSeries D)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  intro k V W M M' θ ψ hθ hP
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (expS D k τ) (expT D k τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd (congrArg dualPar e1) (congrArg dualPar e2)
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' (expS D k) (expT D k) A hC.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => hV V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (hF V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

end GlobalTheory.Chain.RealIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFormsOrth

variable {D : D7}

theorem hO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    hO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.rat_conjTranspose]
  have hz : GlobalTheory.MixModel.rat R * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ) = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, ← Matrix.mul_assoc, h,
      GlobalTheory.MixModel.rat_zero]
  have e : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.rat Qᴴ * GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * (a * GlobalTheory.MixModel.rat R)))
      = GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ * (GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * a)) * GlobalTheory.MixModel.rat R := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero]

theorem symplO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    symplO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.symplO_eq, hO_mul_rat_eq_zero V W a b R Q h, mul_zero, map_zero]

theorem frame_pair (V : HSp D) {r s : ℕ} (C₁ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (C₂ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    adj D C₁ * V.gram * V.gram⁻¹ * (adj D C₂ * V.gram)ᴴ = adj D C₁ * V.gram * C₂ := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]

theorem frame_mid (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (h : adj D C * V.gram * B = 0) :
    adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig] at h ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    GlobalTheory.MixModel.gramInv_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  intro D V V' W r C B hs C' _ hC' hC'B
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  refine ⟨fun a b => ?_, fun a x => ?_, fun a x => ?_, fun a b => ?_⟩
  · exact symplO_mul_rat_eq_zero V W a b (adj D C * V.gram) (adj D C * V.gram) ((frame_pair V C C).trans hC)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C B hs.orth)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C' * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C' B hC'B)
  · exact symplO_mul_rat_eq_zero V W a b (adj D C' * V.gram) (adj D C' * V.gram) ((frame_pair V C' C').trans hC')

end GlobalTheory.TwistFormsOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.LinRed
open scoped InnerProductSpace

namespace GlobalTheory.LeviDense

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

private theorem exists_iteratedDeriv_inner_semigroup_eq {T : ℝ → V →L[ℂ] V} (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0) (w : V) (k : ℕ) :
    ∀ v ∈ S, ∃ u ∈ S, iteratedDeriv k (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t u⟫_ℂ := by
  induction k with
  | zero => intro v hv; exact ⟨v, hv, by simp⟩
  | succ k ih =>
    intro v hv
    obtain ⟨v', hv', hder⟩ := hd v hv
    have hderiv : deriv (fun t => ⟪w, T t v⟫_ℂ) = fun t => ⟪w, T t v'⟫_ℂ := by
      funext t
      have h3 : HasDerivAt (fun s => T (s - t) v) v' t :=
        HasDerivAt.comp_sub_const (f := fun s => T s v) t t (by rw [sub_self]; exact hder)
      have h2 : HasDerivAt (fun s => T t (T (s - t) v)) (T t v') t :=
        ((T t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
      have h1 : HasDerivAt (fun s => T s v) (T t v') t := by
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show T s v = T t (T (s - t) v)
        rw [← ContinuousLinearMap.comp_apply, ← hT, add_sub_cancel]
      exact ((((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1)).deriv
    obtain ⟨u, hu, hk⟩ := ih v' hv'
    exact ⟨u, hu, by rw [iteratedDeriv_succ', hderiv, hk]⟩

theorem oneParameter_mem_closure {T : ℝ → V →L[ℂ] V} (h0 : T 0 = 1) (hT : ∀ s t, T (s + t) = T s ∘L T t)
    {S : Submodule ℂ V} (hd : ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t => T t v) v' 0)
    (ha : ∀ v ∈ S, ∀ w, AnalyticOnNhd ℝ (fun t => ⟪w, T t v⟫_ℂ) Set.univ) (t : ℝ) :
    ∀ v ∈ S.topologicalClosure, T t v ∈ S.topologicalClosure := by
  have key : ∀ v ∈ S, T t v ∈ S.topologicalClosure := by
    intro v hv
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    have hf := ha v hv w
    have hall : ∀ k, iteratedDeriv k (fun s => ⟪w, T s v⟫_ℂ) 0 = 0 := by
      intro k
      obtain ⟨u, hu, hk⟩ := exists_iteratedDeriv_inner_semigroup_eq hT hd w k v hv
      rw [hk]
      simp only [h0, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hu hw
    have htop : analyticOrderAt (fun s => ⟪w, T s v⟫_ℂ) 0 = ⊤ := by
      by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
      have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1)
        (hf 0 (Set.mem_univ _))).2 (fun i _ => hall i)
      rw [← hm] at hle
      have : m + 1 ≤ m := by exact_mod_cast hle
      omega
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
      (analyticOrderAt_eq_top.1 htop) (Set.mem_univ t)
  intro x hx
  have hcl : IsClosed ((T t) ⁻¹' (S.topologicalClosure : Set V)) :=
    S.isClosed_topologicalClosure.preimage (T t).continuous
  have hx' : x ∈ closure (S : Set V) := by rw [← Submodule.topologicalClosure_coe]; exact hx
  exact closure_minimal (fun v hv => key v hv) hcl hx'

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem mul_Jm_comm_of_unitary_of_preserves {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hu : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (hJ : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) :
    A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
  have h2 : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.1 hu
  calc A * Formalism.REAL.Jm ε = A * (Aᴴ * Formalism.REAL.Jm ε * A) := by rw [hJ]
    _ = (A * Aᴴ) * Formalism.REAL.Jm ε * A := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * A := by rw [h2, Matrix.one_mul]

end


omit [CompleteSpace V] in
theorem isKFinOn_of_isKFinIn {n : ℕ} {ε : Fin n → Bool} {M : Subgroup (UJ ε)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} {v : V} (h : IsKFinIn M σ v) : IsKFinOn (mats M) σ v := by
  obtain ⟨U, hU, hv, hk⟩ := h
  refine ⟨U, hU, hv, ?_⟩
  rintro _ ⟨⟨g, hgM, rfl⟩, hgu⟩ w hw
  refine hk g (Subgroup.mem_inf.2 ⟨?_, hgM⟩) w hw
  show toM g ∈ Kset ε
  show toM g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toM g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * toM g
  exact ⟨hgu, mul_Jm_comm_of_unitary_of_preserves ε hgu g.2⟩

end GlobalTheory.LeviDense

end
end

