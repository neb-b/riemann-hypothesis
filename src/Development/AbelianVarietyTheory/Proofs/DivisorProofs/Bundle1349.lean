module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviWeightChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nmat_hasDerivAt (X : Data E r) {f : ℂ → V (nd X)} {f' : V (nd X)} {t : ℂ}
    (hf : HasDerivAt f f' t) (τ : X.Ψ) (a c : Fin r) :
    HasDerivAt (fun s => nmat X (f s) τ a c) (nmat X f' τ a c - if a = c then 1 else 0) t := by
  unfold nmat
  by_cases h : c < a
  · simp only [h, dif_pos, h.ne', if_false, sub_zero]
    exact
      ((PiLp.proj 2 (fun _ : Fin (nd X) => ℂ) ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).hasFDerivAt).comp_hasDerivAt t hf
  · simp only [h, dif_neg, not_false_eq_true, sub_self]
    exact hasDerivAt_const _ _

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a c : Fin r) :
    nmat X 0 τ a c = if a = c then 1 else 0 := by
  have := congrFun (congrFun (IW.nmat_zero X τ) a) c
  simpa [mat, Matrix.one_apply] using this

theorem levi_transport_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  intro E _ _ _ r X x0 x1 b z ho hz hb hxb ξ
  have hz1 : (0 : V (nd X)) ∈ OmF X x1 := IW.zero_mem_OmF X x1 ho
  have hxb' : cpt X x0 z = rmul (cpt X x1 0) b := by rw [IW.cpt_zero]; exact hxb
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 hz1 b hb
  rw [← hxb'] at h0
  have hcd : Differentiable ℂ (cpt X x0) := IW.cpt_diff X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hbz : bf z = b := h0.2.2
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  set v : V (nd X) := WithLp.toLp 2 ξ with hv
  have hγ : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hγU : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ U := by
    have h := (hγ.continuousAt)
    simp only [ContinuousAt, zero_smul, add_zero] at h
    exact h (hU.mem_nhds hzU)
  have hbfD : HasDerivAt (fun t : ℂ => bf (z + t • v)) (fderiv ℂ bf z v) 0 :=
    (hbf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hΦD : HasDerivAt (fun t : ℂ => Φ (z + t • v)) (fderiv ℂ Φ z v) 0 :=
    (hΦ.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hbfE : ∀ τ a c, HasDerivAt (fun t : ℂ => bf (z + t • v) τ a c) (fderiv ℂ bf z v τ a c) 0 :=
    fun τ a c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hbfD τ) a) c
  refine ⟨fun k => (fderiv ℂ Φ z v).ofLp k, fun la => ?_, fderiv ℂ bf z v, ?_, ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
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
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
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
  · intro τ a c hca
    have hev : (fun t : ℂ => bf (z + t • v) τ a c) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hγU] with t ht
      exact ((hsplit _ ht.1 ht.2).2.1 τ).2 a c hca
    exact (hbfE τ a c).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)
  · intro τ
    ext a c
    have hL : HasDerivAt (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c)
        (∑ k, x0 τ a k * (nmat X v τ k c - if k = c then 1 else 0)) 0 :=
      HasDerivAt.fun_sum fun k _ => (nmat_hasDerivAt X hγ τ k c).const_mul _
    have hR : HasDerivAt (fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c)
        (∑ k, ((∑ l, x1 τ a l * (nmat X (fderiv ℂ Φ z v) τ l k - if l = k then 1 else 0)) * bf (z + (0:ℂ) • v) τ k c
          + (∑ l, x1 τ a l * nmat X (Φ (z + (0:ℂ) • v)) τ l k) * fderiv ℂ bf z v τ k c)) 0 :=
      HasDerivAt.fun_sum fun k _ =>
        (HasDerivAt.fun_sum fun l _ => (nmat_hasDerivAt X hΦD τ l k).const_mul _).fun_mul (hbfE τ k c)
    have hev : (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c) =ᶠ[𝓝 0]
        fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c := by
      filter_upwards [hγU] with t ht
      have e0 : cpt X x0 (z + t • v) = rmul (cpt X x1 (Φ (z + t • v))) (bf (z + t • v)) :=
        (hsplit _ ht.1 ht.2).2.2
      have e := congrFun (congrFun (congrFun e0 τ) a) c
      simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at e
      exact e
    have heq := hL.unique (hR.congr_of_eventuallyEq hev)
    simp only [zero_smul, add_zero, hΦz, hbz, nmat_zero_apply] at heq
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, mat, Matrix.of_apply,
      WithLp.toLp_ofLp]
    rw [heq]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

end GlobalTheory.LeviWeightChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOrigin
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviOriginMargin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chain_drop (r p : ℕ) (f : ℕ → ℝ) (g : ℝ)
    (hg : ∀ i, i + 1 < r → i + 1 ≠ p → g ≤ f i - f (i + 1)) :
    ∀ n i, i + n < r → (∀ k, i < k → k ≤ i + n → k ≠ p) → (n : ℝ) * g ≤ f i - f (i + n) := by
  intro n
  induction n with
  | zero => intro i _ _; simp
  | succ n ih =>
    intro i hr hk
    have h1 := ih i (by omega) (fun k h1 h2 => hk k h1 (by omega))
    have h2 := hg (i + n) (by omega) (hk _ (by omega) (by omega))
    have e : i + (n + 1) = i + n + 1 := by omega
    rw [e]
    push_cast
    linarith

theorem coeff_la {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) (hp0 : 0 < X.p0) (hpr : X.p0 < r)
    (hg0 : 0 ≤ g)
    (h1 : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b)
    (h2 : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a)
    (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    g ≤ sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - la τ a) := by
  set f : ℕ → ℝ := fun k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) else 0 with hf
  have hfa : ∀ c : Fin r, f c = la τ c := fun c => by simp [hf, c.isLt]
  have hg : ∀ i, i + 1 < r → i + 1 ≠ X.p0 → g ≤ f i - f (i + 1) := by
    intro i hi hip
    have := h1 τ ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl hip
    simpa [hf, hi, show i < r by omega] using this
  have hch := chain_drop r X.p0 f g hg
  have hab' : (b : ℕ) < a := hab
  have hsame : (∀ k, (b : ℕ) < k → k ≤ b + ((a : ℕ) - b) → k ≠ X.p0) → g ≤ (la τ b : ℝ) - la τ a := by
    intro hk
    have := hch ((a : ℕ) - b) b (by omega) hk
    have e : (b : ℕ) + ((a : ℕ) - b) = a := by omega
    rw [e, hfa, hfa] at this
    have hn : (1 : ℝ) ≤ (((a : ℕ) - b : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (a : ℕ) - b by omega)
    nlinarith
  rcases GlobalTheory.CurvMargin.coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
  · rw [e]; exact hsame (fun k _ hk => by omega)
  · rw [e]; exact hsame (fun k hk _ => by omega)
  · rw [e]

    have hA := hch ((r - 1) - a) a (by omega) (fun k hk _ => by omega)
    have hB := hch (b : ℕ) 0 (by omega) (fun k _ hk => by omega)
    have eA : (a : ℕ) + ((r - 1) - a) = r - 1 := by omega
    rw [eA, hfa] at hA
    rw [zero_add] at hB
    have hB' := hB
    rw [hfa] at hB'
    have h0 := h2 τ ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
    have f0 : f 0 = (la τ ⟨0, by omega⟩ : ℝ) := by simp [hf, show 0 < r by omega]
    have fr : f (r - 1) = (la τ ⟨r - 1, by omega⟩ : ℝ) := by simp [hf, show r - 1 < r by omega]
    have hn1 : (0 : ℝ) ≤ (((r - 1 - a : ℕ)) : ℝ) * g := by positivity
    have hn2 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) * g := by positivity
    rw [fr] at hA
    rw [f0] at hB'
    linarith

theorem coeff_blk {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    0 ≤ sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ∧
    sgn X.p0 a * sgn X.p0 b * ((GlobalTheory.CurvMargin.blockWt X τ b : ℝ) - GlobalTheory.CurvMargin.blockWt X τ a) ≤ 1 := by
  have hab' : (b : ℕ) < a := hab
  unfold GlobalTheory.CurvMargin.blockWt sgn
  by_cases ha : (a : ℕ) < X.p0
  · have hb : (b : ℕ) < X.p0 := hab'.trans ha
    simp [ha, hb]
  · by_cases hb : (b : ℕ) < X.p0
    · simp [ha, hb]
    · simp [ha, hb]

theorem coeff_kap {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin r) (hab : b < a) :
    sgn X.p0 a * sgn X.p0 b * ((kapW X τ b : ℝ) - kapW X τ a) ≤ 2 * r := by
  have hab' : (b : ℕ) < a := hab
  have ha : (a : ℕ) < r := a.isLt
  have hk : ((kapW X τ b : ℝ) - kapW X τ a) = 2 * (b : ℝ) - 2 * (a : ℝ) := by
    simp [kapW]
  rw [hk]
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hba : (b : ℝ) < a := by exact_mod_cast hab'
  have har : (a : ℝ) < r := by exact_mod_cast ha
  unfold sgn
  split_ifs <;> nlinarith

theorem levi_margin_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  intro E _ _ _ r X la x g bb hp0 hpr ho hg0 hbb h1 h2 ξ
  have hs : ∑ j, ‖ξ j‖ ^ 2 = ∑ e : Ent X, ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 :=
    ((Fintype.equivFin (Ent X)).sum_comp (fun j => ‖ξ j‖ ^ 2)).symm
  rw [GlobalTheory.LeviZero.levi_phla_zero r X la x ho ξ, GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    GlobalTheory.LeviZero.levi_phla_zero r X _ x ho ξ,
    hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
  have c1 := coeff_la X la g hp0 hpr hg0 h1 h2 τ a b hab
  have c2 := coeff_blk X τ a b hab
  have c3 := coeff_kap X τ a b hab
  set N := ‖ξ (Fintype.equivFin (Ent X) ⟨τ, ⟨(a, b), hab⟩⟩)‖ ^ 2
  have hN : 0 ≤ N := by positivity
  simp only at c1 c2 c3 ⊢
  nlinarith [mul_nonneg hbb hN, mul_nonneg (mul_nonneg hbb c2.1) hN, mul_nonneg (sub_nonneg.2 c2.2) (mul_nonneg hbb hN),
    mul_nonneg (sub_nonneg.2 c1) hN, mul_nonneg (sub_nonneg.2 c3) hN]

end GlobalTheory.LeviOriginMargin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicative
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviHom

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levi_mul_cols {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b}
    (H : Plane E (b + 2) b) (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h : UA σ W.J) (hL : IsLevi H l g₀ h) :
    mat h * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) =
      fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * blk (mat g₀) l.1 (cA σ (l⁻¹).1) := by
  obtain ⟨hx, hy, hι⟩ := hL
  rw [mul_fromCols, blk, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  refine congrArg₂ fromCols hι ?_
  ext i k
  rw [mul_diagonal]
  fin_cases k
  · have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.x i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · have := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.y i), ← this]; done) | (rw [mul_comm (incV F H.y i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)

theorem isLevi_mul {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b} (H : Plane E (b + 2) b)
    {l l' : (AE F E)ˣ} {g₀ g₀' : UA σ W₁.J} {h h' : UA σ W.J} (hL : IsLevi H l g₀ h) (hL' : IsLevi H l' g₀' h') :
    IsLevi H (l * l') (g₀ * g₀') (h * h') := by
  obtain ⟨hx, hy, hι⟩ := hL
  obtain ⟨hx', hy', hι'⟩ := hL'
  have hm : ∀ (A B : UA σ W.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  have hm₁ : ∀ (A B : UA σ W₁.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ← mulVec_mulVec, hx', mulVec_smul, hx, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← mulVec_mulVec, hy', mulVec_smul, hy, smul_smul, _root_.mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, hm₁, Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]

theorem levi_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    (∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀') ∧ Continuous (fun x : (AE F E)ˣ × UA σ G₁.V.J => m x.1 x.2) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  set QA := Q.map f

  have hform : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h → mat h = PA * blk (mat g₀) l.1 (cA σ (l⁻¹).1) * QA := by
    intro l g₀ h hL
    rw [← levi_mul_cols H l g₀ h hL, Matrix.mul_assoc, hPQ', Matrix.mul_one]
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h h' : UA σ G.V.J), IsLevi H l g₀ h → IsLevi H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by rw [hform l g₀ h hL, hform l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  have hmul : ∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀' := fun l l' g₀ g₀' =>
    huniq _ _ _ _ (hm _ _) (isLevi_mul H (hm l g₀) (hm l' g₀'))
  refine ⟨hmul, ?_⟩
  have m11 : m 1 1 = 1 := by
    have := hmul 1 1 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hinv : ∀ l g₀, (m l g₀)⁻¹ = m l⁻¹ g₀⁻¹ := fun l g₀ =>
    inv_eq_of_mul_eq_one_right (by rw [← hmul, mul_inv_cancel, mul_inv_cancel, m11])
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hmat : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, Continuous fun g : UA σ J => mat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hvec : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ![x.1.1, cA σ (x.1⁻¹).1] := by
    refine continuous_pi fun k => ?_
    fin_cases k
    · exact Units.continuous_val.comp continuous_fst
    · exact hcA.comp (Units.continuous_coe_inv.comp continuous_fst)
  have hval : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2) := by
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) =
        fun x => PA * blk (mat x.2) x.1.1 (cA σ (x.1⁻¹).1) * QA := funext fun x => hform _ _ _ (hm _ _)
    rw [this]
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    exact Continuous.matrix_fromBlocks (hmat.comp continuous_snd) continuous_const continuous_const
      (Continuous.matrix_diagonal hvec)
  have hGL : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E)) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => ((((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E))⁻¹ :
        GL (Fin (b + 2)) (AE F E)) : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))) =
        (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) ∘ fun x => (x.1⁻¹, x.2⁻¹) := by
      funext x
      simp only [Function.comp_apply, ← hinv]
      rfl
    rw [this]
    exact hval.comp ((continuous_inv.comp continuous_fst).prodMk (continuous_inv.comp continuous_snd))
  exact continuous_induced_rng.2 hGL

end GlobalTheory.LeviHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

open scoped TensorProduct Matrix ContDiff

namespace GlobalTheory.LineDerSum


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem skew_of_exp_unitary {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * A * NormedSpace.exp (t • Z) = A) : Zᴴ * A + A * Z = 0 := by
  have h1 : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ = NormedSpace.exp (t • Zᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have hd := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
  have he : ((fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A) * fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A :=
    funext fun t => by rw [Pi.mul_apply, ← h1, h]
  simpa using hd.unique ((hasDerivAt_const (0 : ℝ) A).congr_of_eventuallyEq (.of_forall (congrFun he)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isRealLine_component (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : ℝ → GAd σ J)
    (hc : Continuous δ) (h0 : δ 0 = 1) (hm : ∀ s t, δ (s + t) = δ s * δ t) (w : InfinitePlace F) :
    IsRealLine σ J fun t => embArch σ J w (projArch σ J w (δ t)) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (δ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  refine ⟨w, τ, Z, skew_of_exp_unitary _ _ fun t => ?_, fun t => ⟨_, rfl, hZ t⟩⟩
  rw [← hZ t, GlobalTheory.Orb.archMat_eq_archEquiv J hcm]
  exact (archEquiv J hcm τ _).2

end GlobalTheory.LineDerSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePiece
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

namespace GlobalTheory.DegCmp

theorem rank_map_eq_of_ker_iff {K M A B : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (S : Submodule K M) (f : M →ₗ[K] A) (g : M →ₗ[K] B)
    (h : ∀ x ∈ S, f x = 0 ↔ g x = 0) :
    Module.rank K (S.map f) = Module.rank K (S.map g) := by
  have hk : LinearMap.ker (f.domRestrict S) = LinearMap.ker (g.domRestrict S) := by
    ext x
    simpa using h x x.2
  rw [← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict,
    ← (LinearMap.quotKerEquivRange _).rank_eq, ← (LinearMap.quotKerEquivRange _).rank_eq, hk]

theorem range_pow_eq_map_homogeneous {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) (τ : ℕ) :
    ((LinearMap.range ev) ^ τ : Submodule K Ω) =
      (homogeneousSubmodule (Fin N) K τ).map (aeval (fun j => ev (b j)) : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 3
  ext j
  simp

theorem hilb_eq_finrank_quotPiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  intro K V Ω _ _ _ _ _ ev N b τ
  rw [hilb, range_pow_eq_map_homogeneous ev b τ, GlobalTheory.quotPiece_natCast,
    rank_map_eq_of_ker_iff _ _ (Ideal.Quotient.mkₐ K (imageIdeal ev b)).toLinearMap, ← Module.finrank_eq_rank]
  · simp
  · intro x hx
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_coneIdeal_of_isHomogeneous _ hx).symm

end GlobalTheory.DegCmp
end

