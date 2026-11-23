module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsEnergy
section
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem continuous_hsA_Xop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (μS ν μS' ν' : Measure G) (d : ℝ)
    (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) := by
  have hc : ∀ a : HH, Continuous (fun g => σ g a) := hσ.2.2.2
  unfold hsA Xop sand
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_norm.comp ?_).pow 2
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply]
  exact ((ContinuousLinearMap.adjoint _).continuous.comp (hc _)).const_smul _

theorem lintegral_hsA_Xop {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hSch : IsSchur μ σ d)
    (μS ν μS' ν' : Measure G) (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    ∫⁻ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) ∂μ =
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W A (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' A' (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
  have hd : 0 < d := hSch.1
  have h1 : ∀ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) =
      ENNReal.ofReal (d ^ 2) *
        ENNReal.ofReal (hsA (sand σ (Yop μS ν σ w W A) (Yop μS' ν' σ w W' A') g)) := by
    intro g
    rw [Xop, hsA_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (sq_nonneg d)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_hsA_sand hSch,
    ← ENNReal.ofReal_mul (sq_nonneg d)]
  congr 1
  simp only [Yop_apply_basis]
  field_simp

theorem tendsto_energy {d : ℝ} (hd : 0 < d) {a b : ℕ → ℝ≥0∞} (ha : ∀ n, 0 < a n ∧ a n < ⊤)
    (hb : ∀ n, 0 < b n ∧ b n < ⊤) {N N' : ℕ → ℝ}
    (hN : Tendsto (fun n => N n / (a n).toReal) atTop (𝓝 (1 / d)))
    (hN' : Tendsto (fun n => N' n / (b n).toReal) atTop (𝓝 (1 / d))) :
    Tendsto (fun n => (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n)) atTop (𝓝 (ENNReal.ofReal (1 / d))) := by
  have key : ∀ n, (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n) =
      ENNReal.ofReal (d * (N n / (a n).toReal) * (N' n / (b n).toReal)) := by
    intro n
    obtain ⟨ha0, hat⟩ := ha n
    obtain ⟨hb0, hbt⟩ := hb n
    have ha' : 0 < (a n).toReal := ENNReal.toReal_pos ha0.ne' hat.ne
    have hb' : 0 < (b n).toReal := ENNReal.toReal_pos hb0.ne' hbt.ne
    have hab : (a n * b n)⁻¹ = ENNReal.ofReal (((a n).toReal * (b n).toReal)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (mul_pos ha' hb'), ← ENNReal.toReal_mul,
        ENNReal.ofReal_toReal (ENNReal.mul_ne_top hat.ne hbt.ne)]
    rw [hab, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos ha' hb').le)]
    congr 1
    field_simp
  simp_rw [key]
  apply ENNReal.tendsto_ofReal
  have hlim := (hN.const_mul d).mul hN'
  rwa [show d * (1 / d) * (1 / d) = 1 / d by field_simp] at hlim

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsEquiv
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace HH] in
theorem fY_linear (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p = fY σ w W e p := by
  simp only [fY]
  simp_rw [smul_smul, ← Finset.sum_smul]
  congr 1
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W (p.2⁻¹ * p.1)) e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Yop_apply_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) :
    Yop μS ν σ w W A e = ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A)) := by
  rw [Yop_apply]
  simp_rw [yv_eq_integral hσ hW hinv hA hAS hAf]
  have hint : ∀ i, Integrable (fun p => ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ •
      fY σ w W (stdOrthonormalBasis ℂ V i) p) (ν.prod (μS.restrict A)) :=
    fun i => (integrable_fY hσ hW hinv hA hAS hAf _).smul _
  symm
  calc ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A))
      = ∫ p, ∑ i, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := by
        congr 1
        funext p
        exact (fY_linear σ w W e p).symm
    _ = ∑ i, ∫ p, ⟪stdOrthonormalBasis ℂ V i, e⟫_ℂ • fY σ w W (stdOrthonormalBasis ℂ V i) p
          ∂(ν.prod (μS.restrict A)) := integral_finsetSum _ fun i _ => hint i
    _ = _ := by simp_rw [integral_smul]

omit [SecondCountableTopology G] in
theorem prod_restrict_translate {μS : Measure G} [SFinite μS] (ν : Measure G) [SFinite ν] {s0 : G}
    (hmap : μS.map (fun x => x * s0⁻¹) = μS) (A : Set G) :
    ν.prod (μS.restrict A) =
      (ν.prod (μS.restrict ((fun v => v * s0⁻¹) ⁻¹' A))).map (Prod.map id (fun v => v * s0⁻¹)) := by
  have hE := (MeasurableEquiv.mulRight (s0⁻¹ : G)).measurableEmbedding.restrict_map μS A
  rw [MeasurableEquiv.coe_mulRight, hmap] at hE
  rw [← Measure.map_prod_map ν _ measurable_id (measurable_mul_const s0⁻¹), Measure.map_id, ← hE]

theorem sigma_Yop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν] {S : Set G}
    (hS : IsHaarSub S μS) {d : ℝ} {w : HH} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S) (hAf : μS A < ⊤)
    {s0 : G} (hs0 : s0 ∈ S) (e : V) :
    σ s0⁻¹ (Yop μS ν σ w W A e) =
      Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' A) (ContinuousLinearMap.adjoint (τ s0) e) := by
  obtain ⟨-, -, hmulS, hinvS, hsig, -, -, -, -, hright, -⟩ := hS
  have : SFinite μS := by have := hsig; infer_instance
  have hmap : μS.map (fun x => x * s0⁻¹) = μS := hright _ (hinvS s0 hs0)
  have hA'm : MeasurableSet ((fun v => v * s0⁻¹) ⁻¹' A) := measurable_mul_const s0⁻¹ hA
  have hA'S : (fun v => v * s0⁻¹) ⁻¹' A ⊆ S := by
    intro v hv
    have h1 := hmulS _ (hAS hv) s0 hs0
    simpa [mul_assoc] using h1
  have hA'f : μS ((fun v => v * s0⁻¹) ⁻¹' A) < ⊤ := by
    rw [← Measure.map_apply (measurable_mul_const s0⁻¹) hA, hmap]
    exact hAf
  have hemb : MeasurableEmbedding (Prod.map id (fun v : G => v * s0⁻¹)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulRight s0⁻¹)).measurableEmbedding

  rw [Yop_apply_integral hσ hW hinvS hA hAS hAf, Yop_apply_integral hσ hW hinvS hA'm hA'S hA'f,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_fY hσ hW hinvS hA hAS hAf e),
    prod_restrict_translate ν hmap A, hemb.integral_map]
  congr 1
  funext p
  have hq : (p.2 * s0⁻¹)⁻¹ * p.1 = s0 * (p.2⁻¹ * p.1) := by group
  simp only [fY, Prod.map, id_eq, ContinuousLinearMap.map_smul]
  rw [hq, rep_mul_apply hσ, inv_mul_cancel_left, hW.2.2.2.1 s0 hs0,
    ContinuousLinearMap.adjoint_inner_right]

theorem sand_translate {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite ν'] {S S' : Set G} (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS') {d : ℝ} {w : HH}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    sand σ (Yop μS ν σ w W Ω) (Yop μS' ν' σ w W' Ω') (s0 * γ * s0'⁻¹) =
      (τ s0).comp ((sand σ (Yop μS ν σ w W ((fun v => v * s0⁻¹) ⁻¹' Ω))
        (Yop μS' ν' σ w W' ((fun v => v * s0'⁻¹) ⁻¹' Ω')) γ).comp (ContinuousLinearMap.adjoint (τ' s0'))) := by
  ext b
  refine ext_inner_left ℂ fun a => ?_
  rw [inner_sand]
  conv_rhs => rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, inner_sand]
  rw [← sigma_Yop hσ hS hW hΩm hΩS hΩf hs0 a, ← sigma_Yop hσ hS' hW' hΩm' hΩS' hΩf' hs0' b]
  have hmove : ∀ u : HH, σ γ (σ s0'⁻¹ u) = σ s0⁻¹ (σ (s0 * γ * s0'⁻¹) u) := by
    intro u
    rw [rep_mul_apply hσ, rep_mul_apply hσ, show s0⁻¹ * (s0 * γ * s0'⁻¹) = γ * s0'⁻¹ by group]
  rw [hmove, hσ.2.2.1]

theorem hsA_Xop_translate {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G}
    {μS ν μS' ν' : Measure G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    [SFinite ν] [SFinite ν'] (hσ : IsUnitRep σ) (hS : IsHaarSub S μS) (hS' : IsHaarSub S' μS')
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    {Ω Ω' : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hΩf : μS Ω < ⊤)
    (hΩm' : MeasurableSet Ω') (hΩS' : Ω' ⊆ S') (hΩf' : μS' Ω' < ⊤)
    {s0 s0' : G} (hs0 : s0 ∈ S) (hs0' : s0' ∈ S') (γ : G) :
    hsA (Xop μS ν μS' ν' σ d w W W' Ω Ω' (s0 * γ * s0'⁻¹)) =
      hsA (Xop μS ν μS' ν' σ d w W W' ((fun v => v * s0⁻¹) ⁻¹' Ω) ((fun v => v * s0'⁻¹) ⁻¹' Ω') γ) := by
  simp only [Xop]
  rw [hsA_smul, hsA_smul, sand_translate hσ hS hS' hW hW' hΩm hΩS hΩf hΩm' hΩS' hΩf' hs0 hs0' γ,
    hsA_conj (τ s0) (τ' s0') (hW.2.2.1 s0 hs0) (hW'.2.2.1 s0' hs0')]

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsTail
section
noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def K4 (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V') (γ : G)
    (q : (G × G) × (G × G)) : V' →L[ℂ] V :=
  kG σ d w W W' γ (φinv q.1, φinv q.2)

section Hyp

variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem integrable_liftedRankOneKernel (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    Integrable (K4 σ d w W W' γ) ((ν.prod μS).prod (ν'.prod μS')) := by
  have hi := integrable_kG hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  rw [prod_map_φinv hm hm'] at hi
  exact hi.comp_measurable (Measurable.prodMap (measurable_φinv (G := G)) (measurable_φinv (G := G)))

theorem integral_liftedRankOneKernel [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫ q, K4 σ d w W W' γ q ∂((ν.prod μS).prod (ν'.prod μS')) = ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ := by
  have hi := integrable_kG hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  have hF : Measurable (Prod.map (φinv : G × G → G) (φinv : G × G → G)) :=
    Measurable.prodMap (measurable_φinv (G := G)) (measurable_φinv (G := G))
  have hi' := hi
  rw [prod_map_φinv hm hm'] at hi'
  rw [← integral_kG hσ hW W' γ hi, prod_map_φinv hm hm',
    integral_map hF.aemeasurable hi'.aestronglyMeasurable]
  rfl

theorem prod_restrict_four (A A' : Set G) :
    (ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')) =
      ((ν.prod μS).prod (ν'.prod μS')).restrict ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A')) := by
  have e1 : ν.prod (μS.restrict A) = (ν.prod μS).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have e2 : ν'.prod (μS'.restrict A') = (ν'.prod μS').restrict (Set.univ ×ˢ A') := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e1, e2, Measure.prod_restrict]

end Hyp

section Approx

variable {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
  {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
  {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}

theorem approx_OO [μ.IsMulLeftInvariant] [SFinite μ] (hσ : IsUnitRep σ) (hW : IsWAbs μ σ d w S τ ν W)
    (hW' : IsWAbs μ σ d w S' τ' ν' W') (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤)
    (C C' : ℕ → Set G) (hCm : ∀ n, MeasurableSet (C n)) (hC'm : ∀ n, MeasurableSet (C' n))
    (hCmono : Monotone C) (hC'mono : Monotone C') (hCS : S ⊆ ⋃ n, C n) (hC'S : S' ⊆ ⋃ n, C' n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀, ∀ A A' : Set G, MeasurableSet A → A ⊆ S → μS A < ⊤ → MeasurableSet A' → A' ⊆ S' → μS' A' < ⊤ →
      C n₀ ⊆ A → C' n₀ ⊆ A' →
      Real.sqrt (hsA (∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ)) ≤ ε := by
  set P := (ν.prod μS).prod (ν'.prod μS') with hP
  have hK4 := integrable_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ X : V' →L[ℂ] V, Real.sqrt (hsA X) ≤ c * ‖X‖ :=
    ⟨‖hsC (V := V) (V' := V')‖, norm_nonneg _, fun X => by
      rw [← norm_hsC]
      exact ContinuousLinearMap.le_opNorm _ _⟩
  let Rn : ℕ → Set ((G × G) × (G × G)) := fun n => (Set.univ ×ˢ C n) ×ˢ (Set.univ ×ˢ C' n)
  have hRm : ∀ n, MeasurableSet (Rn n) := fun n =>
    (MeasurableSet.univ.prod (hCm n)).prod (MeasurableSet.univ.prod (hC'm n))
  have hanti : Antitone fun n => (Rn n)ᶜ := fun n m hnm =>
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl (hCmono hnm)) (Set.prod_mono subset_rfl (hC'mono hnm)))
  have hnull : P (⋂ n, (Rn n)ᶜ) = 0 := by
    have hae := ae_mem_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') h0 h0'
    rw [ae_iff] at hae
    refine measure_mono_null (fun p hp => ?_) hae
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hp
    rintro ⟨h1, h2⟩
    obtain ⟨n1, hn1⟩ := Set.mem_iUnion.mp (hCS h1)
    obtain ⟨n2, hn2⟩ := Set.mem_iUnion.mp (hC'S h2)
    exact hp (max n1 n2)
      ⟨⟨trivial, hCmono (le_max_left _ _) hn1⟩, ⟨trivial, hC'mono (le_max_right _ _) hn2⟩⟩
  have hT := tendsto_setIntegral_of_antitone (μ := P) (f := fun q => ‖K4 σ d w W W' γ q‖)
    (fun n => (hRm n).compl) hanti ⟨0, hK4.norm.integrableOn⟩
  rw [setIntegral_measure_zero _ hnull] at hT
  have hT' := hT.const_mul c
  rw [mul_zero] at hT'
  obtain ⟨n₀, hn₀⟩ := (hT'.eventually (gt_mem_nhds hε)).exists
  refine ⟨n₀, fun A A' hA hAS hAf hA' hAS' hAf' hCA hC'A => ?_⟩
  have hR : MeasurableSet (((Set.univ : Set G) ×ˢ A) ×ˢ ((Set.univ : Set G) ×ˢ A')) :=
    (MeasurableSet.univ.prod hA).prod (MeasurableSet.univ.prod hA')
  have hX : Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in (Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'), K4 σ d w W W' γ q ∂P := by
    rw [Xop_eq_integral hσ hW hW' hinv hinv' hA hAS hAf hA' hAS' hAf' γ
      (by rw [prod_restrict_four]; exact hK4.restrict), prod_restrict_four]
    rfl
  have hdiff : ∫ x, rk1A (W x) (W' (γ⁻¹ * x)) ∂μ - Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P := by
    rw [← integral_liftedRankOneKernel hσ hW hW' hinv hinv' h0 h0' hm hm' γ hB, hX, setIntegral_compl hR hK4]
  have hsub : ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ ⊆ (Rn n₀)ᶜ :=
    Set.compl_subset_compl.mpr
      (Set.prod_mono (Set.prod_mono subset_rfl hCA) (Set.prod_mono subset_rfl hC'A))
  rw [hdiff]
  calc Real.sqrt (hsA (∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, K4 σ d w W W' γ q ∂P))
      ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, Real.sqrt (hsA (K4 σ d w W W' γ q)) ∂P :=
        sqrt_hsA_integral_le _ hK4.restrict
    _ ≤ ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, c * ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => Real.sqrt_nonneg _)
          (hK4.norm.const_mul c).restrict (Filter.Eventually.of_forall fun q => hc _)
    _ = c * ∫ q in ((Set.univ ×ˢ A) ×ˢ (Set.univ ×ˢ A'))ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        integral_const_mul c _
    _ ≤ c * ∫ q in (Rn n₀)ᶜ, ‖K4 σ d w W W' γ q‖ ∂P :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hK4.norm.integrableOn
          (Filter.Eventually.of_forall fun q => norm_nonneg _) (Filter.Eventually.of_forall hsub)) hc0
    _ ≤ ε := hn₀.le

end Approx

end Formalism.L2.S.Pv.EnergyAbs
end
end

