module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

section Complex

end Complex

section Adelic

open scoped Classical
open GlobalTheory.RealLift.KLineProof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rho [IsTotallyReal F] (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) ⟨w, IsTotallyReal.isReal w⟩).comp (AlgHom.fst ℝ _ _)

theorem trace_rho [IsTotallyReal F] (v : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) v = ∑ w, rho w v := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}),
    Finset.sum_empty, add_zero]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w) _ _ fun w => ?_
  rw [Algebra.trace_self_apply]
  rfl

theorem rho_evI [IsTotallyReal F] (w : InfinitePlace F) (a : AF F) :
    ((rho w (evI F a) : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  rfl

theorem piInf_algebraMap [IsTotallyReal F] {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = ((rho w (evI F a) : ℝ) : ℂ) := by
  rw [rho_evI]
  change piInf τ (a ⊗ₜ[F] (1 : E)) = _
  rw [piInf_tmul, map_one, mul_one]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  change piInf τ ((1 : AF F) ⊗ₜ[F] e) = _
  rw [piInf_tmul, map_one, map_one, one_mul]

theorem rho_trace [IsTotallyReal F] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : rho w (evI F (Algebra.trace (AF F) (AE F E) z)) = 2 * (piInf τ z).re := by
  have h1 : z + cA σ z = algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) :=
    GlobalTheory.GaussMean.OneVec.add_sigR (AF F) hCM z
  have h2 := congrArg (fun y => (piInf τ y).re) h1
  simp only [map_add (f := _), piInf_cA hCM, piInf_algebraMap, Complex.ofReal_re, Complex.add_re] at h2
  rw [← h2]
  simp [two_mul]

end Adelic

end GlobalTheory.ThK.EvAt0.PlaneQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.ZPartArc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR' {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

end GlobalTheory.ThK.EvAt0.ZPartArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeGeHeightPolynomialVectorsDet
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GlobalTheory.HSShort.DetTop

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ w' : Matrix (Fin n) (Fin N) F, w * w' = 1 := by
  have hr : LinearMap.range w.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hw
  obtain ⟨g', hg'⟩ := w.mulVecLin.exists_rightInverse_of_surjective hr
  refine ⟨LinearMap.toMatrix' g', ?_⟩
  have := congrArg LinearMap.toMatrix' hg'
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' w.mulVecLin = w := LinearMap.toMatrix'_toLin' w
  rwa [e] at this

theorem linSubst_det {F : Type} [Field F] {B N n d : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) :
    linSubst w P.det = (P.map (linSubst w)).det := by
  have := RingHom.map_det (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
    MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom P
  exact this

end GlobalTheory.HSShort.DetTop

namespace GlobalTheory.HSShort.DetTop

theorem arch {F V : Type} [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) {d : ℕ}
    (b : Module.Basis (Fin d) F V) {B N : ℕ} (hN : 0 < N) (σ : F →+* ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.det ≠ 0) (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ)
    (Bd : Fin d → ℝ) (hP : P.det ≠ 0) (hhom : IsMultiHomogeneous a P.det) (hBd : ∀ k, 0 < Bd k)
    (hbd : ∀ k (u : Fin B × Fin N → ℂ), (∀ i, frameNorm A (fun j => u (i, j)) = 1) →
      cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) :
    blockSphereMean B N (linSubst A (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
  haveI := blockSphereMeasure_isProbability (B := B) hN
  have hmap0 : map σ P.det ≠ 0 := fun h =>
    hP (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
  have hf0 : linSubst A (map σ P.det) ≠ 0 :=
    GlobalTheory.HeightUnique.linSubst_ne_zero (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA)) hmap0
  have hfm : IsMultiHomogeneous a (linSubst A (map σ P.det)) :=
    GlobalTheory.HeightUnique.linSubst_homog A (isMultiHomogeneous_map_ring a _ hhom σ)
  have hint := Closed.sphereLogIntegrable B N a _ hf0 hfm
  have hae := ae_blockSphere_eval_ne_zero B N a _ hf0 hfm
  have hpt : ∀ z : BlockSphere B N, eval (blockPoint z) (linSubst A (map σ P.det)) ≠ 0 →
      Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ≤
        ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
    intro z hz
    set u : Fin B × Fin N → ℂ := fun q => A.mulVec (fun k => blockPoint z (q.1, k)) q.2 with hu
    have hunit : ∀ i, frameNorm A (fun j => u (i, j)) = 1 := fun i => by
      show frameNorm A (A.mulVec (fun k => blockPoint z (i, k))) = 1
      rw [GlobalTheory.MaxPoint.frameNorm_mulVec hA]
      have hz := (z i).2
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq] at hz
      simpa [blockPoint, spherePoint] using hz
    have hev : eval (blockPoint z) (linSubst A (map σ P.det)) = (Matrix.of fun i k => eval₂ σ u (P i k)).det := by
      rw [GlobalTheory.MaxPoint.eval_linSubst, MvPolynomial.eval_map]
      have := RingHom.map_det (eval₂Hom σ u) P
      rw [coe_eval₂Hom] at this
      rw [this]; rfl
    rw [hev] at hz ⊢
    obtain ⟨hG, hH⟩ := _root_.GlobalTheory.HSShort.hadamard_basis_comb F V nm d b σ (Matrix.of fun i k => eval₂ σ u (P i k))
    have hprod : ∏ k, cnrm nm σ (fun i => (Matrix.of fun i k => eval₂ σ u (P i k)) i k) b ≤ ∏ k, Bd k :=
      Finset.prod_le_prod₀ (fun k _ => Real.sqrt_nonneg _) (fun k _ => hbd k u hunit)
    have hpos : 0 < ‖(Matrix.of fun i k => eval₂ σ u (P i k)).det‖ := norm_pos_iff.2 hz
    have hsq : 0 < Real.sqrt (nm.gram σ b).det.re := Real.sqrt_pos.2 hG
    have hle := Real.log_le_log (mul_pos hpos hsq) (hH.trans hprod)
    rw [Real.log_mul hpos.ne' hsq.ne', Real.log_prod (fun k _ => (hBd k).ne'), Real.log_sqrt hG.le] at hle
    linarith
  unfold blockSphereMean
  calc ∫ z, Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ∂(blockSphereProb B N)
      ≤ ∫ _z, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2) ∂(blockSphereProb B N) :=
        integral_mono_ae hint (integrable_const _) (by
          filter_upwards [hae] with z hz
          exact hpt z hz)
    _ = _ := by simp

end GlobalTheory.HSShort.DetTop

theorem GlobalTheory.HSShort.deg_ge_ht_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ), Lat w A Λ → ∀ (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ) (Bd : Fin d → ℝ), P.det ≠ 0 → IsMultiHomogeneous a P.det → (∀ k, 0 < Bd k) → (∀ k m, ∑ i, AddMonoidAlgebra.coeff (linSubst w (P i k)) m • b i ∈ M) → (∀ k σ (u : Fin B × Fin N → ℂ), (∀ i, frameNorm (A σ) (fun j => u (i, j)) = 1) → cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) → ht w A P.det - ∑ k, Real.log (Bd k) ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM B N n w A Λ hL P a Bd hP hhom hBd hcoef hbd
  obtain ⟨w', hw'⟩ := GlobalTheory.HSShort.DetTop.exists_rightInv w hL.spans
  have hdet := GlobalTheory.HSShort.DetTop.linSubst_det w P
  have hg0 : linSubst w P.det ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hw' hP
  have hcg : ∀ m, AddMonoidAlgebra.coeff (linSubst w P.det) m ∈
      Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
    rw [hdet]
    exact _root_.GlobalTheory.DetCoeff.coeff_det_mem_span_det F V M d b _ (P.map (linSubst w)) (fun k m => by simpa using hcoef k m)
  have hfin := _root_.GlobalTheory.HSShort.DetIdeal.finPart_sub_mean_le_deg F V nm M d b hM _ _ hg0 hcg
  have harch : ∀ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := fun σ =>
    GlobalTheory.HSShort.DetTop.arch nm b hL.pos σ (A σ) (hL.det σ) P a Bd hP hhom hBd (fun k u hu => hbd k σ u hu)
  have hr : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast NumberField.Embeddings.card F ℂ
  have hht : ht w A P.det = finPart (linSubst w P.det) +
      mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) := by
    simp only [ht, formHeight, finPart, mean, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hmean : mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) ≤
      ∑ k, Real.log (Bd k) - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 := by
    unfold mean
    calc (∑ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det))) / (Module.finrank ℚ F : ℝ)
        ≤ (∑ σ : F →+* ℂ, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2)) / (Module.finrank ℚ F : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => harch σ) hr.le
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.sum_div]
          field_simp
  rw [hht]
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem GlobalTheory.AutGrowth.tame_of_autForm (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hφ : IsAutForm φ) : φ ∈ tame E a := by
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := _root_.GlobalTheory.AutGrowth.ApproxId.exists_approx_identity E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := _root_.GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space hP E a ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

theorem GlobalTheory.AutGrowth.lie_growth_of_finite : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ →
    ∀ g : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(GlobalTheory.CuspRep.lie E a X φ).1 (g * GlobalTheory.CuspRep.infGL E a y)‖ ≤
      C * GlobalTheory.CuspRep.height y ^ N := by
  intro hP E _ _ _ a X φ hφ
  exact growth_of_tame (lie_mem_tame X (GlobalTheory.AutGrowth.tame_of_autForm hP E a φ hφ))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem lintegral_sq_comp_linearEquiv_mixed (F : Type) [Field F] [NumberField F] (κ : Type)
    [Fintype κ] (n : ℕ)
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    ∃ c : ℝ≥0∞, ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ,
      ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 = c * ∫⁻ z, ‖h z‖ₑ ^ 2 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := MeasurableAdd₂.toMeasurableAdd
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let eM := Q.toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n)))).IsAddHaarMeasure :=
    Q.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n))) =
      c • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨(c : ℝ≥0∞), fun h => ?_⟩
  have h1 : ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 =
      ∫⁻ z, ‖h z‖ₑ ^ 2 ∂(Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    rw [lintegral_map_equiv]; rfl
  rw [h1, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLe
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem lintegral_cube_slab_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G)
    (π : G →+ (Fin N → ℝ)) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hS : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ := by
  set S : Set G := {w | w - ι (π w) ∈ U} with hSdef
  let ν : Measure (Fin N → ℝ) := (μ.restrict S).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact lt_top_iff_ne_top.2 (hfin A hA)⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ S)]
    congr 1
    ext w
    simp only [hSdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, map_add (f := _), hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hcube : MeasurableSet (cube N) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume (cube N) = 1 := by
    simp [cube, Real.volume_Icc_pi]
  have hνc : μ (π ⁻¹' cube N ∩ S) = c := by
    rw [← hν _ hcube, hc, Measure.smul_apply, hvol]; simp
  have hf : Measurable fun t => φ (y + ι t) := hφ.comp (measurable_const_add y |>.comp hι.measurable)
  have e1 : ∫⁻ t in cube N, φ (y + ι t) ∂ν = c * ∫⁻ t in cube N, φ (y + ι t) := by
    rw [hc, Measure.restrict_smul, lintegral_smul_measure]; rfl
  rw [hνc, ← e1, setLIntegral_map hcube hf hπ.measurable,
    Measure.restrict_restrict (hπ.measurable hcube)]
  have e2 : ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + ι (π w)) ∂μ = ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ := by
    refine setLIntegral_congr_fun ((hπ.measurable hcube).inter hS) fun w hw => ?_
    have := hper (y + ι (π w)) _ hw.2
    rw [← this]
    congr 1
    abel
  rw [e2]
  calc ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ ≤ ∫⁻ w, φ (y + w) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ w, φ w ∂μ := lintegral_add_left_eq_self φ y

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder Matrix.Norms.L2Operator

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dite_eq_left (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 := by
  let A : Matrix (Fin n) (Fin n) ℂ := (γ.1 : GL (Fin n) E).val.map τ
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom
      (γ.1 : GL (Fin n) E).val * (γ.1 : GL (Fin n) E).val = 1 := by
    have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom
        (γ.1 : GL (Fin n) E).val * 1 * (γ.1 : GL (Fin n) E).val = 1 := γ.2
    simpa only [Matrix.mul_one] using h
  have hstar : star A * A = 1 := by
    have hm := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map τ) hγ
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at hm
    convert hm using 1
    apply congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M * A)
    ext i j
    simp [A, cT, IsCMField.complexEmbedding_complexConj]
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    apply IsUnit.mem_unitary_of_star_mul_self _ hstar
    exact ⟨GeneralLinearGroup.map τ γ.1, rfl⟩
  apply spectrum.norm_eq_one_of_unitary hu
  apply Matrix.mem_spectrum_of_isRoot_charpoly
  apply Polynomial.isRoot_of_mem_roots
  simpa [A, Matrix.charpoly_map] using hz

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_indicator_coset_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 → ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | exact GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | (intros; apply GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum <;> assumption)
end

