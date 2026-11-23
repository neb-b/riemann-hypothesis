module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandKill
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_band :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f h : G → ℂ),
      IsRay N a H → Continuous f → Integrable f μ → Kills μ N a f → IsBand N H h → ∀ x, conv μ f h x = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f h hR hf hfi hK hB x
  have ha := hR.cont
  have hh : Continuous h := hB.1
  obtain ⟨B, hBd⟩ := hB.2.1
  obtain ⟨C, -, hC⟩ := isEig_of_isBand G N a H h hR hB 0
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    simpa using this
  have hFc : Continuous (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) := by fun_prop
  have hF : Integrable (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) (μ.prod volume) := by
    rw [integrable_prod_iff hFc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hC (g⁻¹ * x)).1.const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hFc.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC (g⁻¹ * x)).2 (norm_nonneg _)
  have huc : Continuous (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := by
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * B) (fun t => ?_) (fun t => ?_)
      (hfi.norm.mul_const B) (Eventually.of_forall fun g => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Eventually.of_forall fun g => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _)
  have hui : Integrable (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := hF.integral_prod_right
  have key := fourier_zero _ huc hui (fun s => ?_) 0
  · simpa [a0, conv] using key
  obtain ⟨D, hE, -⟩ := isEig_of_isBand G N a H h hR hB s
  have h0 := hK s D _ hE x
  have hF' : Integrable (fun p : G × ℝ =>
      Complex.exp (-((s * p.2 : ℝ) * Complex.I)) * (f p.1 * h (p.1⁻¹ * x * a p.2))) (μ.prod volume) := by
    refine hF.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => ?_)
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsw := integral_integral_swap (μ := μ) (ν := (volume : Measure ℝ))
    (f := fun g t => Complex.exp (-((s * t : ℝ) * Complex.I)) * (f g * h (g⁻¹ * x * a t))) hF'
  simp only [← integral_const_mul]
  rw [← hsw, ← h0, conv]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.OpLeHalf
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.opLe_half :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∃ s : ℝ, OpLe μ N a f s (1 / 2) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hR hf
  have hU := transl_small G μ f hf 1 one_pos
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨D, hD, hk⟩ := hR.cpt
  have hc : Continuous fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹ :=
    (continuous_snd.mul (hR.cont.comp continuous_fst)).mul continuous_snd.inv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 := by
    apply hD.eventually_forall_of_forall_eventually
    intro k _
    have ht : Tendsto (fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹) (𝓝 (0, k)) (𝓝 1) := by
      have := hc.tendsto (0, k)
      simpa [a0] using this
    exact ht.eventually hU
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (hev'.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := htpos
  refine ⟨Real.pi / t, ?_⟩
  rintro C h ⟨hcont, hbd, hN, hE⟩ x
  obtain ⟨k, hkD, hk⟩ := hk x
  obtain ⟨m, hm, hkm⟩ := hk t
  have hb := ht k hkD
  set b := k * a t * k⁻¹ with hbdef
  have hneg : ∀ g, h (g⁻¹ * b * x) = - h (g⁻¹ * x) := by
    intro g
    have e : g⁻¹ * b * x = g⁻¹ * x * a t * m := by
      rw [mul_assoc, hkm]; simp only [mul_assoc]
    rw [e, hN _ m hm, hE]
    have : Real.pi / t * t = Real.pi := by field_simp
    rw [this, Complex.exp_pi_mul_I]; ring
  have h1 : ∫ g, f (b * g) * h (g⁻¹ * x) ∂μ = - conv μ f h x := by
    have := integral_mul_left_eq_self (μ := μ) (fun g => f g * h (g⁻¹ * b * x)) b
    simp only [mul_inv_rev, inv_mul_cancel_right] at this
    rw [this, conv, ← integral_neg]
    congr 1
    ext g
    rw [hneg]; ring
  have hfb : Integrable (fun g => f (b * g)) μ := hf.comp_mul_left b
  have hmeas : AEStronglyMeasurable (fun g => h (g⁻¹ * x)) μ :=
    (hcont.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
  have i1 : Integrable (fun g => f (b * g) * h (g⁻¹ * x)) μ :=
    hfb.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have i2 : Integrable (fun g => f g * h (g⁻¹ * x)) μ :=
    hf.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have h2 : ∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ = -2 * conv μ f h x := by
    simp only [sub_mul]
    rw [integral_sub i1 i2, h1, conv]; ring
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 1)
  have h3 : ‖∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ‖ ≤ C := by
    calc _ ≤ ∫ g, ‖f (b * g) - f g‖ * C ∂μ := by
          apply norm_integral_le_of_norm_le ((hfb.sub hf).norm.mul_const C)
          refine Eventually.of_forall fun g => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)
      _ = (∫ g, ‖f (b * g) - f g‖ ∂μ) * C := integral_mul_const _ _
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hb hC
      _ = C := one_mul C
  rw [h2, norm_mul] at h3
  simp at h3
  linarith
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Unfold
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_average :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ f ψ : G → ℂ, Continuous f → Integrable f μ → Continuous ψ → HasCompactSupport ψ → ∀ x,
        conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hN hinv hray f ψ hf hfi hψ hψc x
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hn := isBand_of_compact G N a H ν hN hinv hray (fun g => ((‖ψ g‖ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hψ.norm)
    (hψc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp))
  have hb := isBand_of_compact G N a H ν hN hinv hray ψ hψ hψc
  obtain ⟨⟨-, ⟨C, hC⟩, -, -⟩, -⟩ := hn
  have hC' : ∀ g, ∫ m, ‖ψ (g * m)‖ ∂ν ≤ C := by
    intro g
    have h := hC g
    simp only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hc1 : Continuous (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) := by fun_prop
  have h1 : Integrable (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) (μ.prod ν) := by
    rw [integrable_prod_iff hc1.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hb.2 (g⁻¹ * x)).const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hc1.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC' _) (norm_nonneg _)
  have h2 := (integrable_prod_iff h1.swap.aestronglyMeasurable).1 h1.swap
  have key : ∀ m y : G, (x * m * y)⁻¹ * x * m = y⁻¹ := by
    intro m y; group
  have hc3 : Continuous (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) := by fun_prop
  have h3 : Integrable (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) (ν.prod μ) := by
    rw [integrable_prod_iff hc3.aestronglyMeasurable]
    refine ⟨h2.1.mono fun m hm => ?_, h2.2.congr (Eventually.of_forall fun m => ?_)⟩
    · have := hm.comp_mul_left (x * m)
      simpa only [Function.comp, Prod.swap, key, mul_comm (f _)] using this
    · have := integral_mul_left_eq_self (μ := μ) (fun g => ‖f g * ψ (g⁻¹ * x * m)‖) (x * m)
      simp only [key, mul_comm (f (x * m * _))] at this
      simpa only [Function.comp, Prod.swap] using this.symm
  calc conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x
      = ∫ g, ∫ m, f g * ψ (g⁻¹ * x * m) ∂ν ∂μ := by
        simp only [conv, integral_const_mul]
    _ = ∫ m, ∫ g, f g * ψ (g⁻¹ * x * m) ∂μ ∂ν := integral_integral_swap h1
    _ = ∫ m, ∫ y, ψ y⁻¹ * f (x * m * y) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        have := integral_mul_left_eq_self (μ := μ) (fun g => f g * ψ (g⁻¹ * x * m)) (x * m)
        simp only [key, mul_comm (f (x * m * _))] at this
        exact this.symm
    _ = ∫ y, ∫ m, ψ y⁻¹ * f (x * m * y) ∂ν ∂μ := integral_integral_swap h3
    _ = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
        simp only [integral_const_mul]
end

