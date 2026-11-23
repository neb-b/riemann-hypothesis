module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.HasStrictFDerivAtEquiv
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

namespace PointsAbsIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cxHessian_tensor {D : ℕ} {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    cxHessian (fun y' => Real.log ((X.tensor Y).h (γ y'))) y =
      cxHessian (fun y' => Real.log (X.h (γ y'))) y + cxHessian (fun y' => Real.log (Y.h (γ y'))) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (X.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hX (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (Y.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hY (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((X.tensor Y).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (X.h (γ y')) + 1 * Real.log (Y.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (X.pos _ hy'.2).ne' (Y.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simpa only [Complex.ofReal_one, one_smul] using hH

theorem abs_maDensity_le {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L T : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (hT : ∀ j, IsSmoothHerm (T j))
    (hTp : ∀ j, IsSemiPosHerm (T j)) (hLTp : ∀ j, IsSemiPosHerm ((L j).tensor (T j)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hS : IsSheet P Ψ y w γ) :
    |maDensity (fun j y' => pot L j (γ y')) y| ≤
      3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y := by
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0 := by
    filter_upwards [hS.2] with y' hy'
    exact ⟨hy'.1, hy'.2.1.1⟩
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hT j)
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (fun y' => pot L j (γ y')) y with hAdef
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ :=
    fun j => cxHessian (fun y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y with hBdef
  have hHT : ∀ j, (cxHessian (fun y' => Real.log ((T j).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ (T j) y w γ (hT j) (hTp j) hS
  have hHLT : ∀ j, (cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ _ y w γ (hLT j) (hLTp j) hS
  have hB : ∀ j, B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
      cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hLT j) (hT j) hγ
  have hA : ∀ j, cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y =
      A j + cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hL j) (hT j) hγ
  have hle : ∀ j, (B j - A j).PosSemidef := fun j => by
    have e1 : B j - A j = cxHessian (fun y' => Real.log ((T j).h (γ y'))) y +
        cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHT j).add (hHT j)
  have hge : ∀ j, (A j + B j).PosSemidef := fun j => by
    have e1 : A j + B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
        cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHLT j).add (hHLT j)
  have hn : ‖mixedDisc A‖ ≤ 3 ^ e * (mixedDisc B).re :=
    ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le A B hle hge
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [abs_mul, abs_of_nonneg hc]
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * |(mixedDisc A).re|
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (3 ^ e * (mixedDisc B).re) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hn) hc
    _ = 3 ^ e * ((e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc B).re) := by ring

end PointsAbsIntegrable


open PointsAbsIntegrable in
theorem PtsAbsIntegrable.proof (hInt : PtsIntegrableStatement) (hMeas : PtsAbsMeasurable.Statement) :
    PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hTw := SemiPosTwist.proof TorusInvLevi.proof
  choose T hTs hTp hLTp using fun j => hTw K ι (L j) (hL j)
  have hN : ∀ j, IsSmoothHerm (((L j).tensor (T j)).tensor (T j)) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hTs j)) (hTs j)
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have hs : IsSectionOn P A s := ⟨a, ha, hsa, hsP⟩
  set D := regLine A s ⟨a, ha, hsa⟩ 1 with hDdef
  have hD : IsSmoothHerm D := isSmoothHerm_regLine hA one_pos
  have hD1 : IsSectionOn P D 1 := by
    refine ⟨0, fun k => by simp [hDdef, regLine_a], fun m hm k => ?_,
      fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have h1 := hInt K ι P e Ψ _ A s hP hΨ hN hA hs
  have h2 := hInt K ι P e Ψ _ D 1 hP hΨ hN hD hD1

  have key : ∀ y w, |sheetDensity P Ψ (pot L) (logNorm A s) y w| ≤
      3 ^ e * (-2 * sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm D 1) y w -
        sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm A s) y w) := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · simp only [dif_pos hγ]
      set γ := hγ.choose
      have hS : IsSheet P Ψ y w γ := hγ.choose_spec
      have hmem : γ y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hm := abs_maDensity_le hL hTs hTp hLTp hS
      set r := Real.log (D.h (γ y)) with hr
      have hr0 : 0 ≤ r := by
        rw [hr, hDdef, log_regLine_h]
        exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg (secNorm A s (γ y))])) (by norm_num)
      have hgr : logNorm A s (γ y) ≤ r := by
        by_cases h0 : eval (γ y) (map (Int.castRingHom ℂ) s) = 0
        · have : logNorm A s (γ y) = 0 := by simp [logNorm, h0]
          rw [this]
          exact hr0
        · exact logNorm_le_log_regLine_h zero_le_one hmem.1 h0
      have hD1r : logNorm D 1 (γ y) = -r := by
        simp [logNorm, hr, Real.log_inv]
      rw [hD1r]
      have hg : |logNorm A s (γ y)| ≤ 2 * r - logNorm A s (γ y) := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc |logNorm A s (γ y)| * |maDensity (fun j y' => pot L j (γ y')) y|
          ≤ (2 * r - logNorm A s (γ y)) *
              (3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y) :=
            mul_le_mul hg hm (abs_nonneg _) (by linarith [abs_nonneg (logNorm A s (γ y))])
        _ = _ := by ring
    · simp only [dif_neg hγ]
      simp
  refine Integrable.mono' (((h2.const_mul (-2)).sub h1).const_mul (3 ^ e))
    (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) (Eventually.of_forall fun y => ?_)
  have hfin := fibreFinite K ι P e Ψ hP hΨ y
  simp only [Pi.sub_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => key y w

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ProjectionPullbackZeroSetNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem orbit_subsingleton (t : (Σ k', ι' k') → ℂ) :
    {x : R.X | R.lift x x ∉ mcPts J' ∧ SameOrbit (R.lift x x) t}.Subsingleton := by
  rintro x ⟨hx, hxt⟩ x' ⟨-, hx't⟩
  exact R.inj x x' hx (sameOrbit_tr hxt (sameOrbit_comm hx't))

theorem not_flat_pull (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΦ : IsGoodProj (imageZ v P') Φ)
    (j : Fin R.A.n) {O : Set (Fin n → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target)
    (hne : O.Nonempty) (h0 : ∀ u ∈ O, Φ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  classical
  obtain ⟨f, a, hf, hfP, hfin⟩ := hGen K ι K' ι' κ v P' n hv hP' hP
  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J'}) ∩
    ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) with hO'def
  have hO' : IsOpen O' := (hO.inter (isOpen_chart_notB R j)).inter (isOpen_chart_ne R hf j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : O ⊆ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J'}) ∪
        ((R.A.chart j).target ∩
          (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) := by
      intro u hu
      by_cases hB : R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u) ∈ mcPts J'
      · exact Or.inl ⟨hOt hu, hB⟩
      by_cases hF : eval (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))
          (map (Int.castRingHom ℂ) f) = 0
      · exact Or.inr ⟨hOt hu, hF⟩
      have : u ∈ O' := ⟨⟨hu, hOt hu, hB⟩, hOt hu, hF⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty u)
    exact (hO.measure_pos volume hne).ne'
      (measure_mono_null hsub (measure_union_null (R.null j) (fzero_null R hP' hf hfP j)))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono fun u hu => hu.1.1)
    (fun u hu => hdet u hu.1.1)
  have hSinf : ((R.A.chart j).symm '' (O' ∩ (pullQ R v Φ ∘ (R.A.chart j).symm) ⁻¹' {y})).Infinite :=
    Set.Infinite.image ((R.A.chart j).symm.injOn.mono fun u hu => hu.1.1.2.1) hy
  have hF := fibreFinite K ι (imageZ v P') n Φ hP hΦ y
  choose! uw huw using fun w (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Φ y) => hw
  choose T hT using fun w => hfin (uw w)
  refine hSinf ((hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_)
  rintro _ ⟨u, ⟨huO', hqu⟩, rfl⟩
  set x := (R.A.chart j).symm u
  have hxB : R.lift x x ∉ mcPts J' := huO'.1.2.2
  have hxf : eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0 := huO'.2.2
  have h0x : Φ (segre (pullPt R v x)) 0 ≠ 0 := h0 u huO'.1.1
  have hqx : pullQ R v Φ x = y := hqu
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Φ h0x
  rw [hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Φ x)) :=
    sameOrbit_of_segre hu1.1 (Φ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Φ x) (R.lift x x) (R.mem x x (R.mem_U x)) hxf hso
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

theorem projection_pullback_zeroSet_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin n → ℂ) → ℂ := fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0
    with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (IntersectionWithSection.comp_mem_mcPts hv (R.mem x0 x0 (R.mem_U x0)))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (pullPt R v x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin n := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (n + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj (imageZ v P') Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (pullPt R v x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_pullQ R hv Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (pullQ R v Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, pullQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with w hw
        exact hzero w hw
      have hd : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          (0 : (Fin n → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun w => ?_
      have := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ => T w) hrow
      simpa using this
    exact not_flat_pull R hGen hv hP' hP Ψ' hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O
      hanO hdetO
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hwb).2)
    have h := congrArg (fun s => Ψ s 0) hμeq
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
    have hw0' : Ψ (segre (pullPt R v ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hμ

theorem ram_pull_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ
    with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu).1.2)
    rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_pullQ R hv Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat_pull R hGen hv hP' hP Ψ hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_pullQ_chart R hv Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) w :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem pullBad_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0 := by
  have h3 : pullBad R v Ψ ⊆ {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
      {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (pullPt R v x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_pullQ R hv Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (projection_pullback_zeroSet_null R hGen hv hP' hP Ψ hΨ j))
    (ram_pull_null R hGen hv hP' hP Ψ hΨ j)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFibreOverFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def FibreOverFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)), IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (fibreOver v P' W).Finite

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StValCentreZ
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def IsValCentre {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) [P.IsPrime]
    (R : ValuationSubring (FractionRing (MRing ι ⧸ P))) (y : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime y ∧ P ≤ y ∧
    ∀ (b : K → ℕ) (f g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R.nonunits)

def ValCentreZ.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (hP : IsMultiProjPrime P),
    haveI := hP.1
    ∀ R : ValuationSubring (FractionRing (MRing ι ⧸ P)), ∃ y : Ideal (MRing ι), IsValCentre P R y

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def EvalKerKrullDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (F L : Type) [Field F] [Field L] [Algebra F L]
    (y : (Σ k, ι k) → L),
    ringKrullDim (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) =
      ((Algebra.trdeg F (IntermediateField.adjoin F (Set.range y))).toENat : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
end
end

