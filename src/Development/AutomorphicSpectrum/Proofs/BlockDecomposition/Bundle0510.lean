module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousScale
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CoordR

theorem coordInf : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  intro F E _ _ _ _ _ σ hσ n M
  obtain ⟨-, e, -, he, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.real_iso F hσ.1
  let eh : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph _
  have heh : ∀ y, eh y = e y := fun _ => rfl
  haveI : SecondCountableTopology (Ainf F) := eh.secondCountableTopology
  haveI : T2Space (Ainf F) := eh.symm.t2Space
  obtain ⟨i1, i2, i3, i4, -, -, hb, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  let d := Module.finrank F E
  let b : Module.Basis (Fin d) F E := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Ainf F) b
  let Hs : (Ainf F ⊗[F] E) ≃ₜ (Fin d → Ainf F) := (hb d b).homeomorph _
  have hHs : ∀ y k, Hs y k = B.repr y k := fun _ _ => rfl
  let I := Fin n × Fin M × Fin d × InfinitePlace F
  let q : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eH : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin (Fintype.card I) → ℝ) :=
    { toFun := fun X t => eh (Hs (X (q.symm t).1 (q.symm t).2.1) (q.symm t).2.2.1) (q.symm t).2.2.2
      invFun := fun y a j => Hs.symm fun k => eh.symm fun w => y (q (a, j, k, w))
      left_inv := fun X => by simp
      right_inv := fun y => by
        funext t
        simp
      continuous_toFun := continuous_pi fun t =>
        (continuous_apply _).comp (eh.continuous.comp ((continuous_apply _).comp
          (Hs.continuous.comp ((continuous_apply _).comp (continuous_apply _)))))
      continuous_invFun := continuous_pi fun a => continuous_pi fun j =>
        Hs.symm.continuous.comp (continuous_pi fun k => eh.symm.continuous.comp
          (continuous_pi fun w => continuous_apply _)) }
  have hadd : ∀ X Y, eH (X + Y) = eH X + eH Y := by
    intro X Y
    funext t
    change eh (Hs (X _ _ + Y _ _) _) _ = eh (Hs (X _ _) _) _ + eh (Hs (Y _ _) _) _
    simp only [hHs, heh, map_add (f := _), Finsupp.add_apply, Pi.add_apply]
  let eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin (Fintype.card I) → ℝ) :=
    { eH.toEquiv with map_add' := hadd }
  have hV : ∀ X, eV X = eH X := fun _ => rfl
  have hVs : ∀ y, eV.symm y = eH.symm y := fun _ => rfl
  have hc : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      rmul (Ainf F) p.1 p.2 := by
    refine continuous_pi fun a => continuous_pi fun i => continuous_finsetSum _ fun c _ => ?_
    have h1 : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) ×
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => p.1 c i :=
      (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    exact h1.mul (continuous_snd.matrix_elem c a)
  have hrad : ∀ (g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (X Y : Fin n → Fin M → Ainf F ⊗[F] E),
      rmul (Ainf F) (X + Y) g = rmul (Ainf F) X g + rmul (Ainf F) Y g := by
    intro g X Y
    funext a i
    simp [rmul, add_mul, Finset.sum_add_distrib]
  let L0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →+ (Fin (Fintype.card I) → ℝ) :=
    fun g => AddMonoidHom.mk' (fun y => eV (rmul (Ainf F) (eV.symm y) g)) fun y z => by
      rw [map_add (f := _), hrad, map_add (f := _)]
  have hL0 : ∀ g, Continuous (L0 g) := fun g =>
    eH.continuous.comp (hc.comp (eH.symm.continuous.prodMk continuous_const))
  let L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →L[ℝ] (Fin (Fintype.card I) → ℝ) :=
    fun g => (L0 g).toRealLinearMap (hL0 g)
  refine ⟨Fintype.card I, eV, eH.continuous, eH.symm.continuous, L, ?_, ?_⟩
  · refine continuous_clm_apply.2 fun y => ?_
    exact eH.continuous.comp (hc.comp (continuous_const.prodMk continuous_id))
  · intro g X
    change eV _ = eV (rmul (Ainf F) (eV.symm (eV X)) g)
    rw [AddEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.SW.CoordR

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.PushFam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

lemma decay_comp_of_norm_le (g : E → ℂ) (k : ℕ) (C : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) (K : ℝ) :
    ∃ C' : ℝ, ∀ x y : E, ‖y‖ ≤ K * ‖x‖ → ‖g x‖ ≤ C' * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  refine ⟨max C 0 * (1 + |K|) ^ k, fun x y hxy => ?_⟩
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have h2 : 1 + ‖y‖ ≤ (1 + |K|) * (1 + ‖x‖) := by
    have h3 : K * ‖x‖ ≤ |K| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self K) hx
    have h4 : 0 ≤ |K| := abs_nonneg K
    nlinarith
  have h3 : (1 + ‖x‖) ^ (-(k : ℝ)) ≤ (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
      Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (1 + ‖y‖) ^ k ≤ ((1 + |K|) * (1 + ‖x‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
      _ = (1 + |K|) ^ k * (1 + ‖x‖) ^ k := mul_pow _ _ _
  calc ‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(k : ℝ)) := hC x
    _ ≤ max C 0 * (1 + ‖x‖) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    _ = max C 0 * (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by ring

theorem integrable_continuousAt_clm_comp (m : Measure E) (k : ℕ)
    (hW : Integrable (fun y : E => (1 + ‖y‖) ^ (-(k : ℝ))) m)
    (g : E → ℂ) (hg : Continuous g) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)))
    (A₀ : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) (hA₀ : ∀ y, ‖y‖ ≤ M * ‖A₀ y‖) :
    (∀ᶠ A in 𝓝 A₀, Integrable (fun y => g (A y)) m) ∧
      ContinuousAt (fun A : E →L[ℝ] E => ∫ y, g (A y) ∂m) A₀ := by
  have hev : ∀ᶠ A in 𝓝 A₀, ∀ y, ‖y‖ ≤ (2 * M) * ‖A y‖ := by
    filter_upwards [Metric.ball_mem_nhds A₀ (show (0 : ℝ) < 1 / (2 * M) by positivity)] with A hA y
    rw [Metric.mem_ball, dist_eq_norm] at hA
    have e1 : A₀ y = A y - (A - A₀) y := by simp
    have h2 : ‖A₀ y‖ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
      calc ‖A₀ y‖ = ‖A y - (A - A₀) y‖ := by rw [← e1]
        _ ≤ ‖A y‖ + ‖(A - A₀) y‖ := norm_sub_le _ _
        _ ≤ ‖A y‖ + ‖A - A₀‖ * ‖y‖ := by gcongr; exact (A - A₀).le_opNorm y
        _ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
            gcongr
    have h3 : M * (1 / (2 * M) * ‖y‖) = ‖y‖ / 2 := by field_simp
    have h4 := hA₀ y
    have h5 : M * ‖A₀ y‖ ≤ M * ‖A y‖ + ‖y‖ / 2 := by
      rw [← h3, ← mul_add]; exact mul_le_mul_of_nonneg_left h2 hM.le
    linarith
  obtain ⟨C', hC'⟩ := decay_comp_of_norm_le g k C hC (2 * M)
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with A hA
    exact (hW.const_mul C').mono' (hg.comp A.continuous).aestronglyMeasurable
      (ae_of_all _ fun y => hC' _ _ (hA y))
  · refine tendsto_integral_filter_of_dominated_convergence
      (fun y => C' * (1 + ‖y‖) ^ (-(k : ℝ))) ?_ ?_ (hW.const_mul C') (ae_of_all _ fun y => ?_)
    · exact Eventually.of_forall fun A => (hg.comp A.continuous).aestronglyMeasurable
    · filter_upwards [hev] with A hA
      exact ae_of_all _ fun y => hC' _ _ (hA y)
    · exact (hg.comp (continuous_id.clm_apply continuous_const)).continuousAt.tendsto

end GlobalTheory.CompanionTheory.PushFam

namespace GlobalTheory.CompanionTheory.PushFam

theorem integrable_continuousAt_of_linear_push : PositivityTheory.PfSWUS.SchInf.FamCont := by
  intro N X _ μ' hμ' n c O hO hcO hfin hL g hg hdecay
  haveI := hμ'
  set k : ℕ := N + 1 with hk
  set W : (Fin N → ℝ) → ℝ := fun y => (1 + ‖y‖) ^ (-(k : ℝ)) with hWdef
  have hWnonneg : ∀ y, 0 ≤ W y := fun y => by positivity
  have hWμ : Integrable W μ' :=
    integrable_one_add_norm (by rw [Module.finrank_fin_fun, hk]; push_cast; linarith)
  have hWmeas : Measurable W := (measurable_const.add measurable_norm).pow_const _
  obtain ⟨s0, hs0O, hs0fin⟩ := hfin (fun y => ENNReal.ofReal (W y))
    (ENNReal.measurable_ofReal.comp hWmeas)
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).1 hWμ.2).ne O hO ⟨c, hcO⟩
  have hWm : Integrable W (n s0) := ⟨hWmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).2 (lt_top_iff_ne_top.2 hs0fin)⟩
  obtain ⟨L, Linv, Λ, hLc, _hLinvc, hΛc, hinv, hpush⟩ := hL s0 hs0O
  obtain ⟨C, hC⟩ := hdecay k
  have hA₀ : ∀ y, ‖y‖ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := fun y => by
    calc ‖y‖ = ‖Linv c (L c y)‖ := by rw [hinv c hcO]
      _ ≤ ‖Linv c‖ * ‖L c y‖ := (Linv c).le_opNorm _
      _ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := by gcongr; linarith
  obtain ⟨hint, hcont⟩ := integrable_continuousAt_clm_comp (n s0) k hWm g hg C hC (L c)
    (‖Linv c‖ + 1) (by positivity) hA₀
  have hint' : ∀ᶠ s in 𝓝 c, Integrable (fun y => g (L s y)) (n s0) := hLc.eventually hint
  have hO' : O ∈ 𝓝 c := hO.mem_nhds hcO
  refine ⟨?_, ?_⟩
  · filter_upwards [hint', hO'] with s hs hsO
    rw [hpush s hsO]
    exact ((integrable_map_measure hg.aestronglyMeasurable
      (L s).continuous.aemeasurable).2 hs).smul_measure_nnreal
  · have hH : ContinuousAt (fun s => (Λ s : ℝ) • ∫ y, g (L s y) ∂(n s0)) c :=
      (NNReal.continuous_coe.continuousAt.comp hΛc).smul
        (ContinuousAt.comp (f := L) (g := fun A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) =>
          ∫ y, g (A y) ∂(n s0)) hcont hLc)
    refine hH.congr ?_
    filter_upwards [hO'] with s hs
    rw [hpush s hs, integral_smul_nnreal_measure,
      integral_map (L s).continuous.aemeasurable hg.aestronglyMeasurable, NNReal.smul_def]

end GlobalTheory.CompanionTheory.PushFam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

theorem scaleInf : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  intro F E _ _ _ _ _ σ hσ n M μ ν hμ hν
  classical
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨A, hA, hAf⟩ := exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ
  obtain ⟨B, hB, hBf⟩ := exists_scale_herm σ hσ (Ainf F) hR n ν hν
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jB
  haveI := jT2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  refine ⟨A, B, hA, hB, fun g hg => ?_⟩
  have hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    exact continuous_finsetSum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)
  have hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := hTc.measurable
  let τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S =>
    ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩
  have hτ₀c : Continuous τ₀ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
      cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g := fun S => rfl
  have hB0 := hBf g hg τ₀ (fun S => rfl)
  refine ⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩
  · intro h0
    have h1 := hAf g hg
    rw [h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable] at h1
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [h1]; simp)
  · intro h0
    rw [h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable] at hB0
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [hB0]; simp)
  · have : τ = τ₀ := funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)
    rw [this]
    exact hB0

end GlobalTheory.CompanionTheory.SW.HaarScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Summand

variable {D : D7}

theorem trace_inner_join (V : HSp D) {r s : ℕ} (x₁ y₁ : Mx D V.rank r) (x₂ y₂ : Mx D V.rank s) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (colJoin x₁ x₂) (colJoin y₁ y₂)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x₁ y₁) + Matrix.trace (GlobalTheory.StdUnn.inner V x₂ y₂) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]

theorem trace_inner_mul (V : HSp D) {n : ℕ} (U W : Mx D V.rank n) (A A' : Mx D n n)
    (h : HMul.hMul A' (adj A) = (1 : Mx D n n)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A')) = Matrix.trace (GlobalTheory.StdUnn.inner V U W) := by
  have e : GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A') =
      HMul.hMul (adj A) (HMul.hMul (GlobalTheory.StdUnn.inner V U W) A') := by
    simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

theorem inner_neg_left (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (-x) y = -GlobalTheory.StdUnn.inner V x y := by
  have : adj (-x) = -adj x := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (-y) = -GlobalTheory.StdUnn.inner V x y := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem inner_sub_left (V : HSp D) {n : ℕ} (x x' y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (x - x') y = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x' y := by
  have : adj (x - x') = adj x - adj x' := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.sub_mul]

theorem inner_sub_right (V : HSp D) {n : ℕ} (x y y' : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (y - y') = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x y' := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_sub]

theorem inner_zero_left (V : HSp D) {n : ℕ} (y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
  have : adj (0 : Mx D V.rank n) = 0 := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.zero_mul]

theorem inner_mul_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) :
    GlobalTheory.StdUnn.inner V x (HMul.hMul y B) = HMul.hMul (GlobalTheory.StdUnn.inner V x y) B := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_adj {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, adj, map_sum]

theorem adj_inner (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V x y) = GlobalTheory.StdUnn.inner V y x := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) (hB : adj B = B) :
    Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y x) B) =
      cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V x y) B)) := by
  rw [← trace_adj, adj_mul, adj_inner, hB, Matrix.trace_mul_comm]

theorem exp_ring {R : Type*} [CommRing R] (c t₁ t₃ t₄ t₅ : R) (h : c + c = 1) :
    -t₁ + t₅ + c * t₃ + c * t₄ = t₅ + c * (t₃ - t₁ - t₁ + t₄) := by
  linear_combination t₁ * h

theorem sub_group {G : Type*} [AddCommGroup G] (a b c d : G) : a - b - (c - d) = a - b - c + d := by
  abel

theorem halfTr_eq (z : AE D) : halfTr z = algebraMap D.host.F (AF D.host.F) (1 / 2) * trA z := rfl

theorem half_add_half : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_add (f := _), add_halves, map_one]

theorem psi_halfTr_incA (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (e : D.host.E) :
    ψ (halfTr (incA D e)) = 1 := by
  have : halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
    have h : Algebra.trace (AF D.host.F) (AE D) (incA D e) =
        algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
      show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    rw [halfTr_eq, map_mul, trA, h]
  rw [this]
  exact hψ.2.2.1 _

theorem trace_inner_rat (V : HSp D) {n : ℕ} (p : Matrix (Fin V.rank) (Fin n) D.host.E) (b : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ e : D.host.E, Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) = incA D e := by
  refine ⟨Matrix.trace (pᴴ * (HSpace.gram V * p) * b), ?_⟩
  have : HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b) = rat (pᴴ * (HSpace.gram V * p) * b) := by
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, rat, Matrix.map_apply, map_sum]

theorem psi_combine (ψ : AddChar (AF D.host.F) ℂ) (X Y T t₁ t₃ t₄ t₅ : AE D) (e₁ : X = -t₁ + t₅) (e₂ : Y = t₃)
    (e₃ : T = t₃ - cA D t₁ - t₁ + t₄) (e₄ : ψ (halfTr t₄) = 1) :
    ψ (trA X + halfTr Y) = ψ (trA t₅) * ψ (halfTr T) := by
  subst e₁ e₂ e₃
  have h : trA (-t₁ + t₅) + halfTr Y + halfTr t₄ = trA t₅ + halfTr (Y - cA D t₁ - t₁ + t₄) := by
    simp only [halfTr_eq, trA, map_add (f := _), map_sub, map_neg, GlobalTheory.DualPairCheck.trace_cA]
    exact exp_ring _ _ _ _ _ half_add_half
  rw [← AddChar.map_add_eq_mul, ← h, AddChar.map_add_eq_mul ψ _ (halfTr t₄), e₄, mul_one]

theorem summand (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (hb : (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (ha : IsUnit a.det)
    (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s)))
    (hx : xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a))
    (hy : yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹))
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E) :
    Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  have hunit : IsUnit (aᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  have hA : HMul.hMul (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) (adj (rat a)) = (1 : Mx D (r + s) (r + s)) := by
    have : cT (D.sp.cm.sig : D.host.E →+* D.host.E) a = aᴴ := rfl
    rw [this, ← rat_conjTranspose, ← rat_mul, Matrix.nonsing_inv_mul _ hunit, rat_one]
  have hB : adj (rat b) = rat b := by
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hz : rat (colJoin p q * a) = HMul.hMul (colJoin (rat p) (rat q)) (rat a) := by
    rw [rat_mul, rat_colJoin]
  have hzx : rat (colJoin p q * a) + xPart v = HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a) := by
    rw [hz, hx, ← sub_eq_add_neg, ← Matrix.sub_mul, ← colJoin_sub, sub_zero]
  obtain ⟨e, he⟩ := trace_inner_rat V p b
  have e₄ : ψ (halfTr (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)))) = 1 := by
    rw [he]
    exact psi_halfTr_incA ψ hψ e
  have e1 : Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v)) =
      -Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)) + Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) y₂) := by
    rw [hz, hy, trace_inner_mul V _ _ _ _ hA, trace_inner_join, inner_neg_right, inner_mul_right, Matrix.trace_neg]
  have e2 : Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b)) := by
    rw [hx, hy, ← Matrix.neg_mul, trace_inner_mul V _ _ _ _ hA]
    have : -colJoin y₁ (0 : Mx D V.rank s) = colJoin (-y₁) (0 : Mx D V.rank s) := by
      rw [← colJoin_neg, neg_zero]
    rw [this, trace_inner_join, inner_zero_left, inner_neg_left, inner_neg_right, inner_mul_right]
    simp
  have e3 : Matrix.trace (HMul.hMul (rat b) (GlobalTheory.StdUnn.inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b))
        - cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)))
        - Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b))
        + Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) := by
    rw [Matrix.trace_mul_comm, ← trace_swap V (rat p) y₁ (rat b) hB, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [Matrix.sub_mul, Matrix.trace_sub]
    exact sub_group _ _ _ _
  have hc := psi_combine ψ _ _ _ _ _ _ _ e1 e2 e3 e₄
  show ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v))) +
      halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) * Φ (rat (colJoin p q * a) + xPart v) = _
  rw [hc, hzx, mul_assoc]
  rfl

end GlobalTheory.CompanionTheory.EisUnfold.Summand
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotientStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_closed_subgroup_compact_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (S : M → Matrix (Fin n) (Fin n) E) (L : Subgroup (GAd σ J)), IsClosed (L : Set (GAd σ J)) → (∀ g ∈ L, ∀ k, (matHom _ σ J g).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J g).1) → (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ) → (∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ L) → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ L ∧ ∀ g ∈ L, ∃ δ ∈ ratPts σ J, δ ∈ L ∧ δ⁻¹ * g ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | exact GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalRestrictMemCuspidalL2
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open GroundTheory.Automorphic.AutomorphicForm


omit [_root_.NumberField.IsTotallyComplex E] in
theorem unipGL_eq_unip {r : ℕ} (X : UPos a r → Ad E) :
    (unipGL X : GL (Fin a) (Ad E)) = unip X :=
  Units.ext rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isAddHaarMeasure_unipMeasure (r : ℕ) : (unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem ctFun_resQ_eq_zero {φ : GA E a → ℂ} (hφ : φ ∈ cuspCont E a) {r : ℕ} (h0 : 0 < r) (h1 : r < a)
    (y : normOneGL (K := E) (n := a)) : ctFun r (resQ φ) y = 0 := by
  obtain ⟨-, hl, -, hc⟩ := mem_cuspCont.1 hφ
  have h := hc r h0 h1 (unipMeasure E a r) (unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure r) isAddFundamentalDomain_unipFundamentalDomain (y : GA E a)
  unfold ctFun
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)) h
  exact (resQ_mk hl _).trans (congrArg φ (congrArg (· * (y : GA E a)) (unipGL_eq_unip X)))

theorem toLp_restrict_mem_cuspidalL2 (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (φ : GA E a → ℂ) (hφ : φ ∈ cuspCont E a)
    (h : MemLp (resQ φ) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν)) :
    h.toLp (resQ φ) ∈ cuspidalL2 ν := by
  intro r h0 h1
  filter_upwards [ae_ctFun_congr ν r h.coeFn_toLp] with y hy
  exact hy.trans (ctFun_resQ_eq_zero hφ h0 h1 y)

end GlobalTheory.CompanionTheory.CuspTransfer
end

