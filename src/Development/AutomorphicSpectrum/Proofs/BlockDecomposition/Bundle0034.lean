module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormula
section
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_semidirect :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ N M _ _ _ hN hM hgen hdisj νN νM hNH hNR hMH hMR δ hδN hδM q
  haveI := hNH
  haveI := hNR
  haveI := hMH
  haveI := hMR
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set Q))
  haveI : BorelSpace M := Subtype.borelSpace (fun x => x ∈ (M : Set Q))
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements Q N M hN hM hgen hdisj
  let Ψ : (M × N) ≃ₜ Q := (Homeomorph.prodComm M N).trans Φ
  have hΨ : ∀ p : M × N, Ψ p = (p.2 : Q) * (p.1 : Q) := fun p => hΦ (p.2, p.1)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  set ρ : Measure Q := (νM.prod νN).map Ψ with hρ
  have hconj : ∀ (m : Q) (n : N), ((MulAut.conjNormal m n : N) : Q) = m * n * m⁻¹ :=
    fun m n => MulAut.conjNormal_apply m n
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun K hK => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) K = (νM.prod νN) (Ψ ⁻¹' K) from
      Ψ.toMeasurableEquiv.map_apply K]
    have : IsCompact (Ψ ⁻¹' K) := by
      have := hK.image Ψ.symm.continuous
      rwa [Ψ.symm.image_eq_preimage_symm, Ψ.symm_symm] at this
    exact this.measure_lt_top
  haveI : ρ.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) U = (νM.prod νN) (Ψ ⁻¹' U) from
      Ψ.toMeasurableEquiv.map_apply U]
    exact (hU.preimage Ψ.continuous).measure_ne_zero _ (hne.preimage Ψ.surjective)
  haveI : ρ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective g
    have hmul : Measurable (fun y : Q => y * Ψ (m₀, n₀)) := measurable_mul_const _
    have hc : Continuous (fun p : M × N => (MulAut.conjNormal (p.1 : Q) n₀ : N)) := by
      have h : Continuous (fun p : M × N => (p.1 : Q) * n₀ * (p.1 : Q)⁻¹) := by fun_prop
      exact Topology.IsInducing.subtypeVal.continuous_iff.2
        (h.congr fun p => (hconj _ _).symm)
    let T : M × N → M × N := fun p => (p.1 * m₀, p.2 * MulAut.conjNormal (p.1 : Q) n₀)
    have hT : MeasurePreserving T (νM.prod νN) (νM.prod νN) := by
      refine MeasurePreserving.skew_product (f := fun m : M => m * m₀)
        (g := fun (m : M) (n : N) => n * MulAut.conjNormal (m : Q) n₀)
        (measurePreserving_mul_right νM m₀) ?_ (Filter.Eventually.of_forall fun m => ?_)
      · exact (continuous_snd.mul hc).measurable
      · exact (measurePreserving_mul_right νN _).map_eq
    have hcomp : (fun y : Q => y * Ψ (m₀, n₀)) ∘ Ψ = Ψ ∘ T := by
      funext ⟨m, n⟩
      simp only [Function.comp, T, hΨ, Subgroup.coe_mul, hconj]
      group
    rw [hρ, Measure.map_map hmul hΨm, hcomp, ← Measure.map_map hΨm hT.measurable, hT.map_eq]
  refine GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_eq_of_map_left_mul Q ρ δ ?_ q
  intro q₀
  obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective q₀
  have hmul : Measurable (fun y : Q => Ψ (m₀, n₀) * y) := measurable_const_mul _
  have hcm : Continuous (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := by
    have h : Continuous (fun n : N => (m₀ : Q) * n * (m₀ : Q)⁻¹) := by fun_prop
    exact Topology.IsInducing.subtypeVal.continuous_iff.2
      (h.congr fun p => (hconj _ _).symm)
  let f₁ : M → M := fun m => m₀ * m
  let f₂ : N → N := fun n => n₀ * MulAut.conjNormal (m₀ : Q) n
  have hf₁ : Measurable f₁ := measurable_const_mul _
  have hf₂ : Measurable f₂ := (continuous_const.mul hcm).measurable
  have hcomp : (fun y : Q => Ψ (m₀, n₀) * y) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext ⟨m, n⟩
    simp only [Function.comp, Prod.map, f₁, f₂, hΨ, Subgroup.coe_mul, hconj]
    group
  have hνM : νM.map f₁ = νM := (measurePreserving_mul_left νM m₀).map_eq
  have hνN : νN.map f₂ = (δ m₀)⁻¹ • νN := by
    have : f₂ = (fun n : N => n₀ * n) ∘ (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hcm.measurable, hδM _ m₀.2,
      Measure.map_smul (c := (δ m₀)⁻¹) (f := fun x : N => n₀ * x)
        (measurable_const_mul _).aemeasurable,
      (measurePreserving_mul_left νN n₀).map_eq]
  have hδ : δ (Ψ (m₀, n₀)) = δ m₀ := by
    rw [hΨ]
    simp [map_mul, hδN _ n₀.2]
  rw [hρ, Measure.map_map hmul hΨm, hcomp,
    ← Measure.map_map hΨm (hf₁.prodMap hf₂), ← Measure.map_prod_map νM νN hf₁ hf₂, hνM, hνN,
    Measure.prod_smul_right,
    Measure.map_smul (c := (δ m₀)⁻¹) (f := Ψ) hΨm.aemeasurable, hδ]

end GlobalTheory.CompanionTheory.ModChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
section
namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

theorem htLip : PositivityTheory.RgEis.HtLip := by
  intro G _ _ _ Γ K P η hK hI hη C hC
  obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hη.cont.continuousOn
  refine ⟨M, fun g u hu => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  have h1 : η (p * k * u) = η p + η (k * u) := by
    rw [mul_assoc]; exact hη.left p hp _
  have h2 : η (p * k) = η p + η k := hη.left p hp k
  have h3 : η (1 : G) = 0 := by
    have := hη.left 1 P.one_mem 1
    simp only [mul_one] at this
    linarith
  have h4 : η k = 0 := by
    have := hη.right 1 k hk
    rw [one_mul] at this
    rw [this, h3]
  have h5 := hM (k * u) (Set.mul_mem_mul hk hu)
  rw [Real.norm_eq_abs] at h5
  rw [h1, h2, h4]
  simpa using h5

end GlobalTheory.CompanionTheory.RgEis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadicalStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_semidefinite_null_radical : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ x, (B x x).re = 0 → ∀ w, B x w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | exact GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | (intros; apply GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicative
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe

theorem hs_mul_le_mul {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  have key : ∀ i j, ‖(P * Q) i j‖ ^ 2 ≤ (∑ k, ‖P i k‖ ^ 2) * (∑ k, ‖Q k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(P * Q) i j‖ ≤ ∑ k, ‖P i k‖ * ‖Q k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hQ : Formalism.REAL.hs Q = ∑ j, ∑ k, ‖Q k j‖ ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_comm
  rw [hQ]
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j

end GlobalTheory.CompanionTheory.RgHe
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBound
section
open MeasureTheory
open scoped Matrix

namespace GlobalTheory.CompanionTheory.HolMean.GaussianFamily

lemma integrable_gauss_complex {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun w : ℂ => Real.exp (-δ * ‖w‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := (δ : ℂ)) (by simpa using hδ) 0 0
  have h2 := h.norm
  refine h2.congr (ae_of_all _ fun w => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  have : (-(δ : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) = ((-δ * ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2))
      (volume : Measure (Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℂ))
      (f := fun _ (w : ℂ) => Real.exp (-δ * ‖w‖ ^ 2)) fun _ => integrable_gauss_complex hδ
    exact this
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2))
      (volume : Measure (Fin m → Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure (Fin n → ℂ)))
      (f := fun _ (u : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) fun _ => h1
    exact this
  refine h2.congr (ae_of_all _ fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

theorem main : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ →
    (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) →
    ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2)
      (Metric.ball 0 ρ ×ˢ Set.univ) →
    (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) →
    ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) →
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 =
          ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤
          C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  intro m n Φ ρ C δ hρ hδ hd hc hb K hK hK1
  let G : ℂ → (Fin m → Fin n → ℂ) → ℂ := fun z v => K v * Φ z v
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hcv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Continuous (fun v => Φ z v) := fun z hz =>
    hc.comp_continuous (f := fun v : Fin m → Fin n → ℂ => (z, v)) (by fun_prop)
      (fun v => ⟨hz, Set.mem_univ _⟩)
  have hdG : ∀ v, DifferentiableOn ℂ (fun z => G z v) (Metric.ball 0 ρ) := fun v =>
    (hd v).const_mul (K v)
  have hmG : ∀ z ∈ Metric.ball (0 : ℂ) ρ, AEStronglyMeasurable (G z) volume := fun z hz =>
    (hK.mul (hcv z hz)).aestronglyMeasurable
  have hg : Integrable (fun v : Fin m → Fin n → ℂ =>
      C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := (integrable_gauss m n hδ).const_mul C
  have hbG : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ nhds z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v, ‖G z v‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem, _, hg, fun z hz v => ?_⟩
    calc ‖G z v‖ = ‖K v‖ * ‖Φ z v‖ := norm_mul _ _
      _ ≤ 1 * ‖Φ z v‖ := mul_le_mul_of_nonneg_right (hK1 v) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb z hz.2 v
  have hjoint : ∀ r : ℕ, ContinuousOn
      (fun q : (Fin m → Fin n → ℂ) × ℂ => iteratedDeriv r (fun z => Φ z q.1) q.2)
      (Set.univ ×ˢ Metric.ball 0 ρ) := by
    refine GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family (Fin m → Fin n → ℂ)
      (Metric.ball 0 ρ) hU (fun v z => Φ z v) ?_ hd
    exact hc.comp (f := fun q : (Fin m → Fin n → ℂ) × ℂ => (q.2, q.1)) (by fun_prop)
      (fun q hq => ⟨hq.2, Set.mem_univ _⟩)
  refine ⟨ρ, hρ, ?_, fun r => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    exact ((GlobalTheory.CompanionTheory.HolMean.integral_step hU G hdG hmG hbG).1 z hz).differentiableAt.differentiableWithinAt
  · have key := GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral hU r G hdG hmG hbG 0 h0
    refine key.trans (integral_congr_ae (ae_of_all _ fun v => ?_))
    exact iteratedDeriv_const_mul_field (K v) (fun z => Φ z v)
  · exact (hjoint r).comp_continuous (f := fun v : Fin m → Fin n → ℂ => (v, (0 : ℂ)))
      (by fun_prop) (fun v => ⟨Set.mem_univ _, h0⟩)
  · refine ⟨r.factorial * C / (ρ / 2) ^ r, fun v => ?_⟩
    have hR : 0 < ρ / 2 := by positivity
    have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ :=
      Metric.closedBall_subset_ball (by linarith)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
      (C := C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) (f := fun z => Φ z v) r hR
      ((hd v).diffContOnCl_ball hsub)
      (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)) v)
    refine h.trans (le_of_eq ?_)
    ring

end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSeriesUniformTube
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem tubeGood_tsum (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace T] (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ))
    (hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g)
    (hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2)
    (hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) :
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) := by fun_prop
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v τ₀ hτ₀
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hτ₀ g
    have hline : Continuous fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re) :=
      hc.comp (by fun_prop : Continuous fun τ : ℂ => p + τ • v)
    have hS : (fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re)) ⁻¹' V ∈ 𝓝 τ₀ :=
      hline.continuousAt.preimage_mem_nhds hV
    obtain ⟨S, hSsub, hSo, hτS⟩ := mem_nhds_iff.1 hS
    have hd : DifferentiableOn ℂ (fun τ : ℂ => ∑' r, t r (p + τ • v) g) S :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun r => (hhol r g p v).differentiableOn) hSo
        (fun r τ hτ => hb _ (hSsub hτ) g (mem_of_mem_nhds hU) r)
    exact ((hd τ₀ hτS).differentiableAt (hSo.mem_nhds hτS)).differentiableWithinAt
  · rintro ⟨l₀, g₀⟩ ⟨hl₀, -⟩
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl₀ g₀
    have hVl : (fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V ∈ 𝓝 l₀ :=
      hc.continuousAt.preimage_mem_nhds hV
    have hS : ((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U ∈ 𝓝 (l₀, g₀) :=
      prod_mem_nhds hVl hU
    have hd : ContinuousOn (fun y : (ℂ × ℂ) × T => ∑' r, t r y.1 y.2)
        (((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U) :=
      continuousOn_tsum (fun r => (hcont r).continuousOn) hu
        (fun r y hy => hb _ hy.1 _ hy.2 r)
    exact (hd.continuousAt hS).continuousWithinAt
  · intro C hCΩ hC g
    refine hC.induction_on
      (p := fun S => ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ PositivityTheory.RgEis.tube S, ∀ g' ∈ U,
        ‖∑' r, t r l g'‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨Set.univ, univ_mem, 0, fun l hl => hl.elim⟩
    · rintro s s' hss ⟨U, hU, M, hM⟩
      exact ⟨U, hU, M, fun l hl g' hg' => hM l (hss hl) g' hg'⟩
    · rintro s s' ⟨U, hU, M, hM⟩ ⟨U', hU', M', hM'⟩
      refine ⟨U ∩ U', inter_mem hU hU', max M M', ?_⟩
      rintro l (hl | hl) g' hg'
      · exact (hM l hl g' hg'.1).trans (le_max_left _ _)
      · exact (hM' l hl g' hg'.2).trans (le_max_right _ _)
    · intro x hx
      obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom x (hCΩ hx) g
      exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, U, hU, ∑' r, u r, fun l hl g' hg' =>
        tsum_of_norm_bounded hu.hasSum (fun r => hb l hl g' hg' r)⟩
  · intro l hl g
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl g
    exact Summable.of_nonneg_of_le (fun r => norm_nonneg _)
      (fun r => hb l (show (l.1.re, l.2.re) ∈ V from mem_of_mem_nhds hV) g (mem_of_mem_nhds hU) r) hu

end GlobalTheory.CompanionTheory.RgEisCross
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInduction
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem glue_idempotent_property :
    ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' →
        Q (e + e')) →
      (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := by
  intro S _ Q h0 hmul hadd hloc
  let I : Ideal S :=
    { carrier := {x | ∃ e : S, IsIdempotentElem e ∧ Q e ∧ e * x = x}
      zero_mem' := ⟨0, IsIdempotentElem.zero, h0, by simp⟩
      add_mem' := by
        rintro x y ⟨e, he, hQe, hex⟩ ⟨e', he', hQe', hey⟩
        have hee : e * e = e := he
        have hee' : e' * e' = e' := he'
        have h1e : IsIdempotentElem (1 - e) := he.one_sub
        have hg : IsIdempotentElem (e' * (1 - e)) :=
          IsIdempotentElem.mul he' h1e
        have horth : e * (e' * (1 - e)) = 0 := by
          have : e * (e' * (1 - e)) = e' * (e - e * e) := by ring
          rw [this, hee]; simp
        refine ⟨e + e' * (1 - e), ?_, hadd e _ he hg horth hQe (hmul e' _ he' h1e hQe'), ?_⟩
        · show (e + e' * (1 - e)) * (e + e' * (1 - e)) = e + e' * (1 - e)
          have hg' : (e' * (1 - e)) * (e' * (1 - e)) = e' * (1 - e) := hg
          have : (e + e' * (1 - e)) * (e + e' * (1 - e))
              = e * e + 2 * (e * (e' * (1 - e))) + (e' * (1 - e)) * (e' * (1 - e)) := by ring
          rw [this, hee, horth, hg']; simp
        · have h1 : (e + e' * (1 - e)) * x = x := by
            have : (e + e' * (1 - e)) * x = e * x + e' * (x - e * x) := by ring
            rw [this, hex]; simp
          have h2 : (e + e' * (1 - e)) * y = y := by
            have : (e + e' * (1 - e)) * y = e * y + (e' * y) - e * (e' * y) := by ring
            rw [this, hey]; ring
          rw [mul_add, h1, h2]
      smul_mem' := by
        rintro c x ⟨e, he, hQe, hex⟩
        refine ⟨e, he, hQe, ?_⟩
        show e * (c * x) = c * x
        calc e * (c * x) = c * (e * x) := by ring
          _ = c * x := by rw [hex]  }
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨e, he, hem, hQ⟩ := hloc m hm
    exact hem (hIm ⟨e, he, hQ, by rw [show e * e = e from he]⟩)
  have h1 : (1 : S) ∈ I := by rw [htop]; exact Submodule.mem_top
  obtain ⟨e, _, hQ, he1⟩ := h1
  have : e = 1 := by simpa using he1
  exact this ▸ hQ

end GlobalTheory.CompanionTheory.Idem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
section
open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.Eis

theorem tube_isOpen {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) :=
    (Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)
  exact hc.isOpen_preimage Ω hΩ

theorem line_tube_convex {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by
  intro x hx y hy a b ha hb hab
  have key := hc hx hy ha hb hab
  simp only [tube, Set.mem_ofPred_eq] at hx hy key ⊢
  convert key using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.1.re) * hab
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.2.re) * hab

theorem idTube : IdTube := by
  intro X _ _ _ Ω Ω' F F' hΩ hc hΩ' hne hsub hF hF' heq z hz
  obtain ⟨ω, hω⟩ := hne
  set z0 : ℂ × ℂ := ((ω.1 : ℂ), (ω.2 : ℂ)) with hz0
  have hz0' : z0 ∈ tube Ω' := by simpa [tube, hz0] using hω
  have hline : Continuous fun τ : ℂ => z0 + τ • (z - z0) := by fun_prop
  have hDo : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := (tube_isOpen hΩ).preimage hline
  have hDc : Convex ℝ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := line_tube_convex hc z0 (z - z0)
  have h0 : (0 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by
    show z0 + (0 : ℂ) • (z - z0) ∈ tube Ω
    rw [zero_smul, add_zero]
    exact hsub hz0'
  have h1 : (1 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by simpa using hz
  have hA := (hF z0 (z - z0)).analyticOnNhd hDo
  have hA' := (hF' z0 (z - z0)).analyticOnNhd hDo
  have hev : (fun τ : ℂ => F (z0 + τ • (z - z0))) =ᶠ[𝓝 0] (fun τ : ℂ => F' (z0 + τ • (z - z0))) := by
    have hO' : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω'} := (tube_isOpen hΩ').preimage hline
    filter_upwards [hO'.mem_nhds (by simpa using hz0')] with τ hτ
    exact heq hτ
  have := hA.eqOn_of_preconnected_of_eventuallyEq hA' hDc.isPreconnected h0 hev h1
  simpa using this

end GlobalTheory.CompanionTheory.Eis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedArchimedeanCount
section
open NumberField NumberField.mixedEmbedding Module

namespace GlobalTheory.CompanionTheory.IntCount

theorem finite_and_ncard_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
      ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N :=
  _root_.UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le

end GlobalTheory.CompanionTheory.IntCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_functional_open_stabilizer : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by
  first | exact @GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | exact GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | (intros; apply GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegmentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by
  first | exact @GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | exact GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | (intros; apply GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points <;> assumption)
end

