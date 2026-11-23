module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNextStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0138
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.Antisymmetry
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem antisymmetry : Antisymmetry := by
  intro hIn II hII Ψ _ _ _ N j d hN S K _ ι _ P Re hF
  obtain ⟨d₀, S₀, Re₀, hd₀, hdeg₀, href₀, hline₀, ⟨hF₀⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.flagVarieties_flagSys hIn Ψ N hN
  have hdim : d + 1 = antisymDegree Ψ N := hF.dim
  obtain rfl : d = d₀ := by omega
  have hS := ((_root_.GlobalTheory.CompanionTheory.Ar.PB.proportional hIn Ψ N j hN hF.j_le).2 (d + 1) S hdim hF.unif).2
  have hpot := _root_.GlobalTheory.CompanionTheory.Ar.PB.re_pot hIn.2.1.1 (FlBlock Ψ N) (FlIdx Ψ N) (d + 1) (Ψ × Fin N) S₀ (PFl Ψ N) Re₀
  have harith : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
    rw [← hdim]; exact Re₀.arith
  have hfl := flLines_polys hIn II hII Ψ N hN harith

  have hdeg0 : toWt S₀.degPoly = degFlPoly Ψ N := by
    have h2 := hfl.2
    rw [← hdim] at h2
    rw [h2]
    congr 1
    unfold AnSys.degPoly
    congr 1
    funext w
    have h3 := hpot.2.1 w
    simp only [href₀, hdeg₀, Nat.cast_one, one_mul] at h3
    exact h3.symm

  have hPB0 : toWt (Re₀.PB II) = hFlPoly Ψ N II := by
    have h1 := hfl.1
    rw [← hdim] at h1
    rw [h1]
    congr 1
    unfold Realis.PB
    congr 1
    funext w
    unfold Realis.limNum Realis.num
    simp only [hline₀, hdeg₀, Nat.cast_one, div_one]
    exact tendsto_const_nhds.limUnder_eq

  have hdegS : S.degPoly = C (volOf S) * S₀.degPoly := by
    apply (_root_.GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective).2.2 Ψ N
    rw [hS, map_mul, hdeg0]
    congr 1
    simp [toWt, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

  obtain ⟨Cst, hC⟩ := GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound Ψ N (antisymDegree Ψ N + 1)
  have hhomT : (toWt (Re.PB II)).IsHomogeneous (antisymDegree Ψ N + 1) := by
    refine (hC.1 _ 0 ?_).1
    rw [← hdim]
    exact (formPoly_isHomogeneous_and_eval (Ψ × Fin N) (d + 1 + 1) (Re.limNum II)).1
  have hhomH : (hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) :=
    (formPoly_isHomogeneous_and_eval (Ψ × Fin N) _ _).1
  have hhom : (toWt (Re.PB II) - volOf S • hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) := by
    have hm := (homogeneousSubmodule (Ψ × Fin N) ℝ (antisymDegree Ψ N + 1)).sub_mem
      ((mem_homogeneousSubmodule _ _).2 hhomT)
      (Submodule.smul_mem _ (volOf S) ((mem_homogeneousSubmodule _ _).2 hhomH))
    exact (mem_homogeneousSubmodule _ _).1 hm
  refine mem_antisymSpace_of_pointwise Ψ N j _ hhom ?_
  intro τ a b hab hj lam
  have e1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.thmA_swap hIn II hII Ψ N d S K ι P Re τ a b hab (hF.sq τ a b hab hj) lam
  have e0 := _root_.GlobalTheory.CompanionTheory.Ar.PB.thmA_swap hIn II hII Ψ N d S₀ (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) Re₀ τ a b hab
    (hF₀.sq τ a b hab (Or.inl b.isLt)) lam
  rw [hPB0] at e0
  rw [hdegS, (_root_.GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective).2.1, (_root_.GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective).1, Polynomial.eval_mul, Polynomial.eval_C, ← e0] at e1
  simp only [map_sub, smul_eval]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBall
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_prod' {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) U) : DifferentiableOn ℂ (fun t => ∏ i ∈ u, f i t) U :=
  _root_.UpperTheory.Reformulated.B.Yhd5.main u h

theorem differentiableOn_det' {n m : ℕ} {U : Set (Fin n → ℂ)} {M : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ a b, DifferentiableOn ℂ (fun t => M t a b) U) : DifferentiableOn ℂ (fun t => (M t).det) U := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  exact differentiableOn_prod' _ fun i _ => h _ _

theorem chart_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted (F.R 0) A₀ → ∃ (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom F.q) ∧ DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ t ∈ ballDom F.q, ∀ A, C.IsAdapted (F.R t) A → Z t = moebBall F.q (fun τ => C.cinv (A₀ τ) τ * A τ) 0) ∧ ∀ t ∈ ballDom F.q, ballPot F.q (Z t) = ballPot F.q t + (G t).re := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C A₀ h₀
  obtain ⟨hUo, hUc, hU0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero Ψ j j' n F.q
  have hunit : ∀ τ, (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j' := h₀.unit
  have hex : ∀ t, ∃ A, t ∈ ballDom F.q → C.IsAdapted (F.R t) A := fun t => by
    by_cases ht : t ∈ ballDom F.q
    · obtain ⟨A, hA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted.exists_isAdapted E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨A₀, fun h => absurd h ht⟩
  choose Ad hAd using hex

  let dV : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ :=
    fun τ b t => C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))
  let aV : Ψ → Fin j → (Fin n → ℂ) → Fin g → ℂ :=
    fun τ i t => C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim (Pi.single i 1) 0)
  let Wm : (Fin n → ℂ) → Ψ → Matrix (Fin j') (Fin j) ℂ := fun t τ => moebW (C.cinv (A₀ τ) τ * Ad t τ) 0
  have hgA := fun t (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : C.IsAdapted (F.R t) A) =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.gram_last_block E Ψ j j' n g Λ F C (F.R t) A (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.im_perExt_eq_Fm E Ψ j j' n g Λ F C (F.R t) (F.form_eq t)) hA
  have hpt := fun t (ht : t ∈ ballDom F.q) τ =>
    GlobalTheory.T.adapted_frame_ball_coordinate E Ψ j j' n g Λ F C (F.R t) (Ad t) A₀ τ (Wm t τ) (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.sgU_blocks j j') (hgA t (Ad t) (hAd t ht) τ) (hAd t ht) (hunit τ) rfl

  have hgram : ∀ t ∈ ballDom F.q, ∀ τ, IsUnit (F.R t |>.gram fun b => dV τ b t).det := by
    intro t ht τ
    have h := (hpt t ht τ).2.1
    have hc : ((2 * C.c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos two_pos C.c_pos).ne'
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (h2 ▸ pow_ne_zero _ hc))
  have hind : ∀ t ∈ ballDom F.q, ∀ τ, LinearIndependent ℂ (fun b => dV τ b t) := fun t ht τ =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.linearIndependent_of_isUnit_gram_det E g Λ (F.R t) j' _ (hgram t ht τ)

  have hrel : ∀ t, ∀ τ (W : Matrix (Fin j') (Fin j) ℂ),
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) → ∀ i,
      -aV τ i t = ∑ b, W b i • dV τ b t := by
    intro t τ W hW i
    have h := hW (Pi.single i 1)
    rw [pPart_elim] at h
    have hWv : ∀ b, (W *ᵥ Pi.single i 1) b = W b i := by
      intro b; simp
    simp only [hWv, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    exact (eq_neg_of_add_eq_zero_right h).symm ▸ by simp [aV, dV]

  have huniq : ∀ t ∈ ballDom F.q, ∀ τ (W W' : Matrix (Fin j') (Fin j) ℂ),
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) →
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W' *ᵥ v)) = 0) → W = W' := by
    intro t ht τ W W' hW hW'
    ext b i
    have h1 := hrel t τ W hW i
    have h2 := hrel t τ W' hW' i
    have h3 : ∑ b, (W b i - W' b i) • dV τ b t = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
    have := Fintype.linearIndependent_iff.1 (hind t ht τ) _ h3 b
    exact sub_eq_zero.1 this

  have hdV : ∀ τ b, DifferentiableOn ℂ (dV τ b) (ballDom F.q) := fun τ b =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.pPart_differentiableOn E Ψ j j' n g Λ F C τ _
  have haV : ∀ τ i, DifferentiableOn ℂ (aV τ i) (ballDom F.q) := fun τ i =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.pPart_differentiableOn E Ψ j j' n g Λ F C τ _

  have hWd : ∀ τ i, DifferentiableOn ℂ (fun t b => Wm t τ b i) (ballDom F.q) := fun τ i =>
    GlobalTheory.T.holomorphic_coefficients_in_frame n j' g _ (fun b => dV τ b) (fun t => -aV τ i t) (fun t b => Wm t τ b i) hUo (hdV τ) (haV τ i).neg
      (fun t ht => hind t ht τ) (fun t ht => hrel t τ _ (hpt t ht τ).1 i)

  have hY : ∀ t τ b, ∃ c : Fin j' → ℂ, t ∈ ballDom F.q → dV τ b t = ∑ i, c i • F.b τ i t := by
    intro t τ b
    by_cases ht : t ∈ ballDom F.q
    · have hm : dV τ b t ∈ Submodule.span ℂ (Set.range fun i => F.b τ i t) := by
        rw [((F.frames.2 t ht τ).2)]
        exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.pPart_mem_eigSp_all E Ψ j j' n g Λ F C (F.R t) τ _
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hm
      exact ⟨c, fun _ => hc.symm⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose Yc hYc using hY
  let Ym : (Fin n → ℂ) → Ψ → Matrix (Fin j') (Fin j') ℂ := fun t τ => Matrix.of fun c b => Yc t τ b c
  have hYd : ∀ τ b, DifferentiableOn ℂ (fun t => Yc t τ b) (ballDom F.q) := fun τ b =>
    GlobalTheory.T.holomorphic_coefficients_in_frame n j' g _ (F.b τ) (dV τ b) (fun t => Yc t τ b) hUo (F.frames.1 τ) (hdV τ b)
      (fun t ht => (F.frames.2 t ht τ).1) (fun t ht => hYc t τ b ht)

  have hloc := fun t (ht : t ∈ ballDom F.q) τ =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.PointLog.log_det_change E g Λ (F.R t) j' (fun i => F.b τ i t) (fun b => dV τ b t) (Ym t τ) (1 - Wm t τ * (Wm t τ)ᴴ) (2 * C.c)
      (mul_pos two_pos C.c_pos) (fun b => hYc t τ b ht) (hpt t ht τ).2.1 (hpt t ht τ).2.2

  let Pf : (Fin n → ℂ) → ℂ := fun t => ∏ τ, (Ym t τ).det
  have hPd : DifferentiableOn ℂ Pf (ballDom F.q) := by
    refine differentiableOn_prod' _ fun τ _ => differentiableOn_det' fun a b => ?_
    exact (differentiableOn_pi.1 (hYd τ b)) a
  have hP0 : ∀ t ∈ ballDom F.q, Pf t ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.2 fun τ _ => (hloc t ht τ).1
  obtain ⟨G₀, hG₀a, hG₀⟩ := GroundTheory.Heights₂.Heights.Regular.exists_analytic_log hUo hUc ⟨0, hU0⟩
    (ReciprocityTheory.AnForm.Osgood.osgood n _ Pf hUo hPd) hP0
  have hG₀d : DifferentiableOn ℂ G₀ (ballDom F.q) := hG₀a.differentiableOn
  refine ⟨fun t => ballPt F.q (Wm t), fun t => 2 * G₀ t - ((Fintype.card Ψ * j' * Real.log (2 * C.c) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine differentiableOn_pi.2 fun k => ?_
    exact (differentiableOn_pi.1 (hWd _ _)) _
  · exact (hG₀d.const_mul 2).sub_const _
  · intro t ht A hA
    have hb0 : ∀ τ, ballMat F.q 0 τ = 0 := fun τ => by ext a b; simp [ballMat]
    have : (fun τ => Wm t τ) = fun τ => moebW (C.cinv (A₀ τ) τ * A τ) ((ballMat F.q 0 τ)ᵀ) := by
      funext τ
      rw [hb0, Matrix.transpose_zero]
      exact huniq t ht τ _ _ (hpt t ht τ).1
        (GlobalTheory.T.adapted_frame_ball_coordinate E Ψ j j' n g Λ F C (F.R t) A A₀ τ _ (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.sgU_blocks j j') (hgA t A hA τ) hA (hunit τ) rfl).1
    simp only [moebBall]
    exact congrArg (ballPt F.q) this
  · intro t ht
    have hre : (G₀ t).re = ∑ τ, Real.log ‖(Ym t τ).det‖ := by
      have h1 : ‖Pf t‖ = Real.exp (G₀ t).re := by rw [← hG₀ t ht, Complex.norm_exp]
      have h2 : Real.log ‖Pf t‖ = (G₀ t).re := by rw [h1, Real.log_exp]
      rw [← h2, norm_prod, Real.log_prod]
      intro τ _
      exact norm_ne_zero_iff.2 (hloc t ht τ).1
    rw [_root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.ballPot_ballPt_eq, ← F.logDet_eq t ht]
    simp only [RiemLat.logDet, ← Finset.sum_neg_distrib]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, zero_mul, sub_zero, hre]
    rw [Finset.sum_congr rfl fun τ _ => (hloc t ht τ).2]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

