module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandCc
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology Pointwise

theorem UpperTheory.Lit.Cusp.isBand_of_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ →
        IsBand N H (fun g => ∫ m, ψ (g * m) ∂ν) ∧ ∀ g, Integrable (fun m => ψ (g * m)) ν := by
  intro G _ _ _ _ _ _ _ _ N a H ν _ hN hinv hray ψ hψ hc
  have hint : ∀ g, Integrable (fun m => ψ (g * m)) ν := fun g =>
    (hψ.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.mulLeft g))
  have hcont : Continuous (fun g => ∫ m, ψ (g * m) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds g₀
    have hk : IsCompact (U⁻¹ * tsupport ψ) := hU.inv.mul hc
    have h := continuousOn_integral_of_compact_support (μ := ν) (f := fun g m => ψ (g * m)) (s := U) hk
      (hψ.comp (continuous_fst.mul continuous_snd)).continuousOn (fun p x hp hx => by
        by_contra hne
        exact hx ⟨p⁻¹, Set.inv_mem_inv.2 hp, p * x, subset_tsupport ψ hne, by simp⟩)
    exact h.continuousAt hUn
  have hI : ∀ g, ∀ m ∈ N, (∫ x, ψ (g * m * x) ∂ν) = ∫ x, ψ (g * x) ∂ν := by
    intro g m hm
    have h := integral_map_equiv (μ := ν) (MeasurableEquiv.mulLeft m) (fun x => ψ (g * x))
    have h2 : ν.map (MeasurableEquiv.mulLeft m) = ν := hinv m hm
    rw [h2] at h
    rw [h]
    simp [mul_assoc]
  have hex : ∀ g, (∫ m, ψ (g * m) ∂ν) ≠ 0 → ∃ m ∈ N, g * m ∈ tsupport ψ := by
    intro g hg
    by_contra hne
    apply hg
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ m ∂ν, m ∈ N := hN
    filter_upwards [hae] with m hm
    by_contra h0
    exact hne ⟨m, hm, subset_tsupport ψ h0⟩
  refine ⟨⟨hcont, ?_, hI, ?_⟩, hint⟩
  · obtain ⟨C, hC⟩ := (IsCompact.image hc hcont.norm).bddAbove
    refine ⟨max C 0, fun g => ?_⟩
    by_cases hg : (∫ m, ψ (g * m) ∂ν) = 0
    · simp [hg]
    · obtain ⟨m, hm, hs⟩ := hex g hg
      have := hC ⟨g * m, hs, rfl⟩
      simp only [hI g m hm] at this
      exact this.trans (le_max_left _ _)
  · obtain ⟨R, hR⟩ := (IsCompact.image hc hray.contH.abs).bddAbove
    refine ⟨R, fun g hg => ?_⟩
    obtain ⟨m, hm, hs⟩ := hex g hg
    have := hR ⟨g * m, hs, rfl⟩
    simpa only [hray.inv g m hm] using this
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvAssoc
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_assoc :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (e f h : G → ℂ) (C : ℝ),
      Continuous e → Integrable e μ → Continuous f → Integrable f μ → Continuous h → (∀ g, ‖h g‖ ≤ C) →
      (∀ x, conv μ e f x = f x) → ∀ x, conv μ f h x = conv μ e (conv μ f h) x := by
  intro G _ _ _ _ _ _ _ _ μ _ e f h C _ hei _ hfi hh hC hef x
  have h1 : Integrable (fun z : G × G => e z.1 * f z.2) (μ.prod μ) := hei.mul_prod hfi
  have h2 : Integrable (fun z : G × G => e z.1 * f (z.1⁻¹ * z.2)) (μ.prod μ) :=
    (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable h1
  have h3 : Integrable (fun z : G × G => e z.1 * f (z.1⁻¹ * z.2) * h (z.2⁻¹ * x)) (μ.prod μ) := by
    refine h2.mul_bdd (c := C) ?_ (Eventually.of_forall fun z => hC _)
    exact (hh.comp (continuous_snd.inv.mul continuous_const)).aestronglyMeasurable
  have h4 : ∀ g : G, conv μ f h (g⁻¹ * x) = ∫ y, f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self (fun y => f (g⁻¹ * y) * h (y⁻¹ * x)) g]
    simp only [conv, inv_mul_cancel_left, mul_inv_rev, mul_assoc]
  calc conv μ f h x = ∫ y, ∫ g, e g * f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ ∂μ := by
        unfold conv
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [integral_mul_const, ← hef y]
        rfl
    _ = ∫ g, ∫ y, e g * f (g⁻¹ * y) * h (y⁻¹ * x) ∂μ ∂μ :=
        (integral_integral_swap (f := fun g y => e g * f (g⁻¹ * y) * h (y⁻¹ * x)) h3).symm
    _ = conv μ e (conv μ f h) x := by
        show _ = ∫ g, e g * conv μ f h (g⁻¹ * x) ∂μ
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        beta_reduce
        rw [h4, ← integral_const_mul]
        simp only [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvEig
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_isEig :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (f h : G → ℂ) (s C : ℝ),
      Integrable f μ → IsEig N a s C h → IsEig N a s ((∫ g, ‖f g‖ ∂μ) * C) (conv μ f h) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a f h s C hf hh
  obtain ⟨hc, hb, hN, ha⟩ := hh
  have hbound : ∀ x g, ‖f g * h (g⁻¹ * x)‖ ≤ ‖f g‖ * C := fun x g => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hint : Integrable (fun g => ‖f g‖ * C) μ := hf.norm.mul_const C
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * C) ?_ ?_ hint ?_
    · intro x
      refine hf.aestronglyMeasurable.mul ?_
      exact (hc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    · intro x
      exact Eventually.of_forall (hbound x)
    · refine Eventually.of_forall fun g => ?_
      exact continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  · intro x
    unfold conv
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le hint (Eventually.of_forall (hbound x))
  · intro x m hm
    unfold conv
    simp only [← mul_assoc, hN _ m hm]
  · intro x t
    unfold conv
    rw [← integral_const_mul]
    congr 1
    funext g
    rw [← mul_assoc, ha]
    ring
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EigBand
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.isEig_of_isBand :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (N : Set G) (a : ℝ → G) (H : G → ℝ) (h : G → ℂ),
      IsRay N a H → IsBand N H h → ∀ s : ℝ, ∃ C : ℝ,
        IsEig N a s C (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) ∧
          ∀ g, Integrable (fun t : ℝ => h (g * a t)) ∧ ∫ t : ℝ, ‖h (g * a t)‖ ≤ C := by
  intro G _ _ _ _ _ _ N a H h hr hb s
  obtain ⟨hc, ⟨B, hB⟩, hN, ⟨R, hR⟩⟩ := hb
  have ha := hr.cont
  have hH := hr.contH
  have he1 : ∀ x : ℝ, ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := fun x => by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsupp : ∀ g t, h (g * a t) ≠ 0 → |H g + t| ≤ R := fun g t hne => by
    have := hR _ hne
    rwa [hr.move] at this
  have hint : ∀ g, Integrable (fun t : ℝ => h (g * a t)) := by
    intro g
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -R - H g) (b := R - H g)) ?_
    intro t ht
    by_contra hne
    apply ht
    have := abs_le.mp (hsupp g t hne)
    constructor <;> linarith [this.1, this.2]
  have hbound : ∀ g, ∫ t : ℝ, ‖h (g * a t)‖ ≤ 2 * |R| * |B| := by
    intro g
    have hle : ∀ t, ‖h (g * a t)‖ ≤ (Set.Icc (-R - H g) (R - H g)).indicator (fun _ => |B|) t := by
      intro t
      by_cases hne : h (g * a t) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g t hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    refine (integral_mono (hint g).norm
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hle).trans ?_
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.volume_real_Icc]
    have h1 : max (R - H g - (-R - H g)) 0 ≤ 2 * |R| :=
      max_le (by linarith [le_abs_self R]) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg B)
  have hshift : ∀ g, (∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
      Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
        ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    intro g
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_sub_right_eq_self _ (H g)]
    congr 1
    ext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hΦ : Continuous fun g =>
      ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    refine continuous_of_dominated (bound := (Set.Icc (-R) R).indicator (fun _ => |B|)) ?_ ?_ ?_ ?_
    · intro g
      exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g))).aestronglyMeasurable
    · intro g
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, he1, one_mul]
      by_cases hne : h (g * a (t - H g)) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g _ hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact Eventually.of_forall fun t => by fun_prop
  refine ⟨2 * |R| * |B|, ⟨?_, ?_, ?_, ?_⟩, fun g => ⟨hint g, hbound g⟩⟩
  · rw [show (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
        fun g => Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
          ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) from funext hshift]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul hΦ
  · intro g
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound g))
    congr 1
    ext t
    rw [norm_mul, he1, one_mul]
  · intro g m hm
    beta_reduce
    congr 1
    ext t
    rw [show g * m * a t = g * a t * ((a t)⁻¹ * m * a t) by group, hN _ _ (hr.norm t m hm)]
  · intro g u
    beta_reduce
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_left_eq_self _ u]
    congr 1
    ext t
    rw [mul_assoc g, ← hr.add, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EqZeroOfTest
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.eq_zero_of_test :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ), Continuous F →
      (∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ → ∫ y, ψ y⁻¹ * F y ∂μ = 0) → ∀ y, F y = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ F hF h y₀
  by_contra hy
  obtain ⟨χ, hχc, hχ0, hχy⟩ := exists_continuous_nonneg_pos y₀
  have hχcont : Continuous (fun y => χ y) := χ.continuous
  have hc1 : Continuous (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    (Complex.continuous_ofReal.comp hχcont).mul (Complex.continuous_conj.comp hF)
  have hs0 : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hs1 : HasCompactSupport (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    hs0.mul_right (f' := fun y => (starRingEnd ℂ) (F y))
  have h1 := h (fun z => (χ z⁻¹ : ℂ) * (starRingEnd ℂ) (F z⁻¹)) (hc1.comp continuous_inv)
    (hs1.comp_homeomorph (Homeomorph.inv G))
  have h2 : ∀ y, (χ y⁻¹⁻¹ : ℂ) * (starRingEnd ℂ) (F y⁻¹⁻¹) * F y
      = ((χ y * ‖F y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [inv_inv, mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [h2] at h1
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
  have hc2 : Continuous (fun y => χ y * ‖F y‖ ^ 2) := hχcont.mul (hF.norm.pow 2)
  have hs2 : HasCompactSupport (fun y => χ y * ‖F y‖ ^ 2) :=
    hχc.mul_right (f' := fun y => ‖F y‖ ^ 2)
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := y₀) hs2
    (fun y => mul_nonneg (hχ0 y) (sq_nonneg _))
    (mul_ne_zero hχy (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)))
  exact hpos.ne' h1
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsCompactTail
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

private theorem exists_compact_tail {G : Type} [TopologicalSpace G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ)
    (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Set G, IsCompact D ∧ ∫ g, Dᶜ.indicator (fun g => ‖f g‖) g ∂μ ≤ ε := by
  have hm : ∀ n, MeasurableSet (compactCovering G n)ᶜ := fun n =>
    (isCompact_compactCovering G n).isClosed.measurableSet.compl
  have ht : Tendsto (fun n => ∫ g, (compactCovering G n)ᶜ.indicator (fun g => ‖f g‖) g ∂μ) atTop
      (𝓝 (∫ _g, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun g => ‖f g‖)
      (fun n => (hf.norm.indicator (hm n)).aestronglyMeasurable) hf.norm (fun n => ?_) ?_
    · refine Eventually.of_forall fun g => ?_
      simpa using norm_indicator_le_norm_self (s := (compactCovering G n)ᶜ) (fun g => ‖f g‖) g
    · refine Eventually.of_forall fun g => ?_
      obtain ⟨n, hn⟩ := exists_mem_compactCovering g
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with m hm'
      have : g ∈ compactCovering G m := compactCovering_subset G hm' hn
      simp [this]
  rw [integral_zero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds hε)).exists
  exact ⟨_, isCompact_compactCovering G n, hn⟩

private theorem isEig_twist {G : Type} [Group G] [TopologicalSpace G] {N : Set G} {a : ℝ → G} {H : G → ℝ}
    (hr : IsRay N a H) {s s' C : ℝ} {h : G → ℂ} (hh : IsEig N a s' C h) :
    IsEig N a s C (fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g) := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hH := hr.contH
  refine ⟨by fun_prop, fun g => ?_, fun g m hm => ?_, fun g t => ?_⟩
  · rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]; exact h2 g
  · simp only [hr.inv g m hm, h3 g m hm]
  · simp only [hr.move g t, h4 g t]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem UpperTheory.Lit.Cusp.opLe_near :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s s' r : ℝ, |s - s'| < δ → OpLe μ N a f s r → OpLe μ N a f s' (r + ε) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hr hf ε hε
  obtain ⟨D, hD, hDε⟩ := exists_compact_tail μ f hf (ε / 4) (by positivity)
  obtain ⟨c, hc⟩ := hr.bdd D hD
  have hmD : MeasurableSet Dᶜ := hD.isClosed.measurableSet.compl
  set A : ℝ := ∫ g, ‖f g‖ ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun g => norm_nonneg _
  set δ : ℝ := ε / 2 / ((|c| + 1) * (A + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : δ * ((|c| + 1) * (A + 1)) = ε / 2 := by rw [hδ]; field_simp
  refine ⟨δ, hδ0, fun s s' r hs hop C h hh x => ?_⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hh.2.1 1)
  have ht := isEig_twist (s := s) hr hh
  have h1 := hop C _ ht x
  have hint : ∀ {t : ℝ} {k : G → ℂ}, IsEig N a t C k → Integrable (fun g => f g * k (g⁻¹ * x)) μ := by
    intro t k hk
    have hk1 := hk.1
    have hc : Continuous fun g : G => k (g⁻¹ * x) := by fun_prop
    exact hf.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun g => hk.2.1 _)
  set u : ℂ := Complex.exp (Complex.I * ((-((s - s') * H x) : ℝ) : ℂ)) with hu
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  set k : G → ℂ := fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g with hk
  have hdiff : u * conv μ f k x - conv μ f h x
      = ∫ g, (u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)) ∂μ := by
    rw [integral_sub ((hint ht).const_mul u) (hint hh), integral_const_mul]
    rfl
  have hpt : ∀ g, ‖u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)‖
      ≤ C * (δ * (|c| + 1) * ‖f g‖ + 2 * Dᶜ.indicator (fun g => ‖f g‖) g) := by
    intro g
    have e : u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)
        = h (g⁻¹ * x) * ((Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1) * f g) := by
      have : Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ))
          = u * Complex.exp (Complex.I * (((s - s') * H (g⁻¹ * x) : ℝ) : ℂ)) := by
        rw [hu, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [this, hk]; ring
    rw [e, norm_mul, norm_mul]
    refine mul_le_mul (hh.2.1 _) ?_ (by positivity) hC
    by_cases hg : g ∈ D
    · have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (s - s') * (H (g⁻¹ * x) - H x))
      have h3 : ‖(s - s') * (H (g⁻¹ * x) - H x)‖ ≤ δ * (|c| + 1) := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hs.le ((hc g hg x).trans (by linarith [le_abs_self c])) (abs_nonneg _) hδ0.le
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = 0 := by simp [hg]
      rw [h4, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg _)
    · have h2 : ‖Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = ‖f g‖ := by simp [hg]
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (f g))
      have h6 : 0 ≤ δ * (|c| + 1) * ‖f g‖ := by positivity
      linarith
  have hi1 : Integrable (fun g => δ * (|c| + 1) * ‖f g‖) μ := hf.norm.const_mul _
  have hi2 : Integrable (fun g => 2 * Dᶜ.indicator (fun g => ‖f g‖) g) μ :=
    (hf.norm.indicator hmD).const_mul _
  have hb : ‖u * conv μ f k x - conv μ f h x‖ ≤ C * ε := by
    rw [hdiff]
    refine (norm_integral_le_of_norm_le ((hi1.add hi2).const_mul C) (Eventually.of_forall hpt)).trans ?_
    simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul, integral_const_mul, ← hA]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have : 0 ≤ δ * (|c| + 1) := by positivity
    nlinarith
  have h2 : ‖u * conv μ f k x‖ ≤ r * C := by rw [norm_mul, hu1, one_mul]; exact h1
  have h3 : ‖conv μ f h x‖ ≤ ‖u * conv μ f k x‖ + ‖u * conv μ f k x - conv μ f h x‖ := by
    simpa using norm_sub_le (u * conv μ f k x) (u * conv μ f k x - conv μ f h x)
  linarith
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Fourier
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

open scoped FourierTransform in
theorem UpperTheory.Lit.Cusp.fourier_zero :
    ∀ u : ℝ → ℂ, Continuous u → Integrable u →
      (∀ s : ℝ, ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * u t = 0) → ∀ t, u t = 0 := by
  intro u hc hi hz t
  have hF : 𝓕 u = 0 := by
    ext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hz (2 * Real.pi * w)]
    congr 1
    ext v
    rw [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  simp [Real.fourierInv_eq]
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Transl
section
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.transl_small :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ), Integrable f μ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b in 𝓝 (1 : G), ∫ g, ‖f (b * g) - f g‖ ∂μ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ μ _ f hf ε hε
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hm : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  set F : Lp ℂ 1 μ := hm.toLp f with hF
  have hc : Continuous fun b : G => ‖(DomMulAct.mk b) • F - F‖ :=
    ((DomMulAct.continuous_mk.smul continuous_const).sub continuous_const).norm
  have h1 : ‖(DomMulAct.mk (1 : G)) • F - F‖ < ε := by
    have : (DomMulAct.mk (1 : G)) • F = F := one_smul Gᵈᵐᵃ F
    rw [this, sub_self, norm_zero]; exact hε
  have hev := hc.continuousAt.eventually_lt continuousAt_const h1
  filter_upwards [hev] with b hb
  refine le_of_eq_of_le ?_ hb.le
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have hFf : F =ᵐ[μ] f := hm.coeFn_toLp
  have h2 : (fun g => F (b * g)) =ᵐ[μ] fun g => f (b * g) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae_eq_comp hFf
  filter_upwards [Lp.coeFn_sub ((DomMulAct.mk b) • F) F, DomMulAct.smul_Lp_ae_eq (DomMulAct.mk b) F, hFf, h2] with g e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, ← e4]
  rfl
end

