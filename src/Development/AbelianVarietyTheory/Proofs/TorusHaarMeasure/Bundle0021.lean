module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BorelDiagNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviTransfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem borel_diag_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  have hdet := (hb τ).1
  have htri : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  rw [Matrix.det_of_upperTriangular htri] at hdet
  exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)


omit [NumberField E] [IsCMField E] in
theorem borel_char_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (la : Wt Ψ r) : bchar la b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    zpow_ne_zero _ (borel_diag_ne_zero hb τ i)


omit [NumberField E] [IsCMField E] in
theorem left_act_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1) * mat x τ :
    Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem normFactor_pos {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos
    (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _

theorem metric_rmul (h : NfacRmulStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phla X la (rmul x b) = phla X la x + Real.log (Complex.normSq (bchar la b)) := by
  have h1 := normFactor_pos X la hx
  have h2 : 0 < ‖bchar la b‖ := norm_pos_iff.2 (borel_char_ne_zero hb la)
  unfold phla
  rw [h r X la x hx b hb, Real.log_mul (inv_pos.2 h2).ne' h1.ne', Real.log_inv,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

theorem levi_transfer :
    (KapGGStatement (E := E)) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) := by
  intro hK hN r X x0 z hz
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hz
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hcd : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c =>
      (IW.cpt_entry_cd X x0 τ a c).differentiable (by simp)
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter
      (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hdet := hK r X x0 x1 1 U Φ bf hU hΦ (fun w hw =>
    ⟨hw.1, (hsplit _ hw.1 hw.2).2.1, by
      rw [left_act_one]; exact (hsplit _ hw.1 hw.2).2.2⟩) z hzU
  have hdet' : (fderiv ℂ Φ z).det ≠ 0 := by
    rw [hdet]; exact borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    have hu : IsUnit ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet')
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨x1, (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).toLinearMap ∘ₗ
    ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.toLinearMap, ho, ?_, ?_⟩
  · exact (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).injective.comp
      (hinj.comp (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.injective)
  intro la ξ
  have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
    classical
    intro w hw
    unfold bchar
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
      fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
      fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
    have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
      differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
    have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
      differentiableAt_zpow.2 (Or.inl (borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
    exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
  have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
    (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
  have hne : bchar la (bf z) ≠ 0 := borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
    rw [← metric_rmul hN.1 X la h1 h2, ← h3]
  have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
    rw [hΦz]
    exact (IW.phla_cpt_cdAt X x1 (IW.zero_mem_OmF X x1 ho) la).of_le HE.two_le_inf
  have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
    hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
    (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
  have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
  rw [hΦz] at hc
  unfold leviM
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
    HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
  exact congrArg Complex.re hc

end GlobalTheory.LeviTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
section
namespace GlobalTheory.KronMetric

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inv_rmul {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : ψ (rmul x b) = ψ x := by
  have := h 1 X.Γ.one_mem x hx b hb
  rwa [FundSetPf.lact_one] at this

theorem inv_lact {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : ψ (lact γ x) = ψ x := by
  have := h γ hγ x hx _ (ExtFPf.oneF_mem X)
  rwa [ExtFPf.rmul_oneF] at this

theorem continuousOn_of_charts {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ)
    (hs : ∀ x0, IsOrth X x0 → ContinuousOn (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContinuousOn ψ X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxe⟩ := ortho_holds r X x hx
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x1 ho
  have h0 : (0 : V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact IW.orth_mem_dom X x1 ho
  have hΔ : D.Δ x ≠ 0 := by
    have := (D.uniq 0 h0 b hb).1
    rwa [IW.cpt_zero, ← hxe] at this
  have hc : ContinuousOn (fun y => ψ (cpt X x1 (D.zOf y))) (ExtFPf.cell D) :=
    (hs x1 ho).comp D.hz.continuousOn fun y hy => (D.split y hy.1 hy.2).1
  have hc' : ContinuousOn ψ (ExtFPf.cell D) := by
    refine hc.congr fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := D.split y hy.1 hy.2
    show ψ y = ψ (cpt X x1 (D.zOf y))
    conv_lhs => rw [h3]
    exact inv_rmul h h1 h2
  exact (hc'.continuousAt ((ExtFPf.isOpen_cell D).mem_nhds ⟨hx, hΔ⟩)).continuousWithinAt

theorem exp_neg_phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem exp_neg_add {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    Real.exp (-(phla X la x + ψ x)) = X.nfac la x ^ 2 * Real.exp (-ψ x) := by
  rw [neg_add, Real.exp_add, exp_neg_phla X la hx]

theorem kronMetric :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) := by
  rintro ⟨hR, hL, -⟩ r X la ψ hinv hs ⟨C, hC⟩
  classical
  have hψc : ContinuousOn ψ X.dom := continuousOn_of_charts hinv fun x0 h => (hs x0 h).continuousOn
  refine ⟨hψc, ⟨?_, ?_, ?_⟩, Real.exp (-C), Real.exp_pos _, ?_⟩
  · have hc : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (((ExtFPf.nfac_contOn X la).pow 2).mul
        (Real.continuous_exp.comp_continuousOn hψc.neg)).congr fun x hx => ?_
      exact exp_neg_add X la ψ hx
    rw [← Set.piecewise_eq_indicator]
    exact hc.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet
  · intro x hx b hb
    have hxb := OntoS.dom_rmul X hx hb
    have hpos : 0 < ‖bchar la b‖ := norm_pos_iff.2 (OntoE.bchar_ne X la hb)
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hx, exp_neg_add X la ψ hxb,
      exp_neg_add X la ψ hx, hR r X la x hx b hb, inv_rmul hinv hx hb,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro γ hγ x hx
    have hγx := OntoS.dom_lact X hγ hx
    rw [Set.indicator_of_mem hγx, Set.indicator_of_mem hx, exp_neg_add X la ψ hγx,
      exp_neg_add X la ψ hx, hL r X la γ hγ x hx, inv_lact hinv hγ hx]
  · intro x hx
    rw [Set.indicator_of_mem hx, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    linarith [hC x hx]

end GlobalTheory.KronMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetFderivNeZeroOrbit
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrbitCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem rmul_left_cancel {r : ℕ} {Ψ : Finset (E →+* ℂ)} {o a c : Frame Ψ r}
    (ho : ∀ τ, (mat o τ).det ≠ 0) (h : rmul o a = rmul o c) : a = c := by
  funext τ
  have h1 : mat o τ * mat a τ = mat o τ * mat c τ := congrFun h τ
  have hu : IsUnit (mat o τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ho τ))
  exact hu.mul_left_cancel h1

theorem exists_swap {r : ℕ} (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ (U : Set (V (nd X))) (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r),
      IsOpen U ∧ 0 ∈ U ∧ DifferentiableOn ℂ Φ U ∧ Φ 0 = 0 ∧
      ∀ z ∈ U, bf z ∈ Bor X.Ψ r ∧ rmul b (nmat X z) = rmul (nmat X (Φ z)) (bf z) := by
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hod : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X (x0F X) ho
  have hcd := OntoB.cd_cpt X (rmul (x0F X) b)
  have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
  rw [IW.cpt_zero] at h0
  refine ⟨cpt X (rmul (x0F X) b) ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0},
    fun z => zOf (cpt X (rmul (x0F X) b) z), fun z => bOf (cpt X (rmul (x0F X) b) z), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((FourierCoefficientDomain.isOpen_dom X).inter
      (isOpen_ne_fun hΔ.continuous continuous_const)).preimage hcd.continuous
  · show cpt X _ 0 ∈ X.dom ∧ Δ (cpt X _ 0) ≠ 0
    rw [IW.cpt_zero]
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  · exact hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  · show zOf (cpt X _ 0) = 0
    rw [IW.cpt_zero]
    exact h0.2.1
  · intro z hzU
    obtain ⟨-, h2, h3⟩ := hsplit _ hzU.1 hzU.2
    refine ⟨h2, rmul_left_cancel (fun τ => (hod τ).1) ?_⟩
    rw [← ExtFPf.rmul_assoc, ← ExtFPf.rmul_assoc]
    exact h3

theorem det_fderiv_ne_zero_orbit : (KapGGStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X))) 0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X))) 0).det ≠ 0) := by
  intro hK r X L w0 s hw0 hs x hx hwx hdet γ hγ b hb
  obtain ⟨U, Φ, bf, hU, h0U, hΦ, hΦ0, hsw⟩ := exists_swap X hb
  set y := lact γ (rmul x b) with hy
  have hyd : y ∈ X.dom := OntoS.dom_lact X hγ (OntoS.dom_rmul X hx hb)
  have hcpt : ∀ z ∈ U, cpt X y z = lact γ (rmul (cpt X x (Φ z)) (bf z)) := by
    intro z hz
    unfold cpt
    rw [hy, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, (hsw z hz).2, ExtFPf.rmul_assoc]
  have h0y : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have h0x : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bf 0) :=
    hK r X y x γ (U ∩ OmF X y) Φ bf (hU.inter (OntoB.isOpen_OmF X y)) (hΦ.mono Set.inter_subset_left)
      (fun z hz => ⟨hz.2, (hsw z hz.1).1, hcpt z hz.1⟩) 0 ⟨h0U, h0y⟩
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsw 0 h0U).1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x ∈ 𝓝 (0 : V (nd X)) := (OntoB.isOpen_OmF X x).mem_nhds h0x
  set F : V (nd X) → V (nd X) := fun z : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F 0 := by
    have hw : DifferentiableAt ℂ (fun z => w0 (cpt X x z)) 0 :=
      (OntoB.hol_comp X x hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun z => s k (cpt X x z)) 0 := fun k =>
      (OntoB.hol_comp X x (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have hne : w0 (cpt X x 0) ≠ 0 := by rwa [IW.cpt_zero]
    have := (hsk k).mul (hw.inv hne)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y z) / w0 (cpt X y z) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), Φ z ∈ OmF X x :=
      hΦd.continuousAt.preimage_mem_nhds (by rwa [hΦ0])
    filter_upwards [hU.mem_nhds h0U, h1] with z hz hzx
    have hzx' : cpt X x (Φ z) ∈ X.dom := hzx
    have hbz := (hsw z hz).1
    have hd := OntoS.dom_rmul X hzx' hbz
    have hχ : X.χ L γ ≠ 0 := by
      intro h
      have := OntoE.chi_norm X L hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    show _ = F (Φ z)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    rw [hcpt z hz, (hs k).2.2 γ hγ _ hd, hw0.2.2 γ hγ _ hd, mul_div_mul_left _ _ hχ,
      (hs k).2.1 _ hzx' _ hbz, hw0.2.1 _ hzx' _ hbz, mul_div_mul_left _ _ (OntoE.bchar_ne X L hbz)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F 0).comp (fderiv ℂ Φ 0)).det = (fderiv ℂ F 0).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

end GlobalTheory.OrbitCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrthNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.OrthNear.isOrth_x0F {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth
  intro τ
  generalize_proofs h
  exact (h τ).choose_spec.2

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem mat_cpt_eq_mat_mul_mat_nmat {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_mul_apply_eq_sum {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M N : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * N) = Matrix.of fun a b =>
      ∑ c, ∑ d, N c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G M c d * starRingEnd ℂ (N d b) := by
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * N) a = ∑ c, N c a • _root_.ReciprocityTheory.ChartRestriction.G.FD.col M c := by
    intro a
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mulVec_eq_sum_col]
    ext k
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, hcol, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_chartCoord_orthonormal_indep_lemma {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ) := by
  have hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) :=
    (hx τ).trans (hy τ).symm
  rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, gram_mul_apply_eq_sum, gram_mul_apply_eq_sum, hx']


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.OrthNear.dmin_cpt_eq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ i := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_chartCoord_orthonormal_indep_lemma X hx hy z τ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem densF_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y z := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem nfac_cpt_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem cpt_mem_dom_iff_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z ∈ X.dom := by
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ).det ≠ 0 ↔
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, Matrix.det_mul, Matrix.det_mul]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hx τ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hy τ]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_setOf_eq, hdet,
    _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.OrthNear.orthNear : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ c ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ≤ C ∧ c ≤ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∧ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ≤ C) := by
  intro r X la
  set x0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 := _root_.GlobalTheory.OrthNear.isOrth_x0F X
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.mp (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X x0) 0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF X x0 h0)
  set K := Metric.closedBall (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (ρ0 / 2)
  have hKsub : K ⊆ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨0, Metric.mem_closedBall_self (by linarith)⟩
  have hd : ContinuousOn (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) K := (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  have hn : ContinuousOn (fun z => X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) K :=
    (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont X x0 la).mono hKsub
  obtain ⟨z1, hz1, hmin1⟩ := hK.exists_isMinOn hKne hd
  obtain ⟨z2, hz2, hmin2⟩ := hK.exists_isMinOn hKne hn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hd
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hn
  refine ⟨ρ0 / 2, min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 z1) (X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z2)), max C1 C2,
    by linarith, lt_min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hKsub hz1)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X x0 (hKsub hz2)), ?_⟩
  intro x hx z hz
  have hzK : z ∈ K := Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hz.le)
  have hdom : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hKsub hzK
  rw [densF_eq_of_isOrth X hx h0, nfac_cpt_eq_of_isOrth X hx h0,
    cpt_mem_dom_iff_of_isOrth X hx h0]
  exact ⟨hdom, (min_le_left _ _).trans (isMinOn_iff.mp hmin1 z hzK),
    (Real.le_norm_self _).trans ((hC1 z hzK).trans (le_max_left _ _)),
    (min_le_right _ _).trans (isMinOn_iff.mp hmin2 z hzK),
    (Real.le_norm_self _).trans ((hC2 z hzK).trans (le_max_right _ _))⟩

end GlobalTheory.OrthNear
end

