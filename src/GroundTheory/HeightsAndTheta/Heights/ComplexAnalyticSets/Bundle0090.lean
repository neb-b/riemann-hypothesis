module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamCritNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Metric Matrix ComplexSets

theorem ParamCritNull.proof : ParamCritNull.Statement := by
  intro n d W A σ r N hW hdim hA hσ hinj hN hZ
  have hg : DifferentiableOn ℂ (fun v => A *ᵥ σ v) (ball (0 : Fin d → ℂ) r) := by
    have hL : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
    exact hL.comp_differentiableOn hσ
  set Ω : Set (Fin d → ℂ) := ball (0 : Fin d → ℂ) r ∩ σ ⁻¹' N with hΩdef
  have hΩ : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage isOpen_ball hN
  rcases Set.eq_empty_or_nonempty Ω with hemp | hne
  · have hsub : {w | w ∈ ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} ⊆ Ω :=
      fun w hw => ⟨hw.1, hw.2.1⟩
    rw [hemp] at hsub
    rw [Set.subset_empty_iff.mp hsub, measure_empty]

  have hsome : ∃ w ∈ ball (0 : Fin d → ℂ) r,
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hrank : ∀ v ∈ Ω, ¬ Function.Injective (fderiv ℂ (fun v => A *ᵥ σ v) v) := by
      intro v hv hinjv
      have h0 := hcon v hv.1
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
      exact h0 (LinearMap.ker_eq_bot.mpr hinjv)
    obtain ⟨y, hy⟩ := IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof d d Ω (fun v => A *ᵥ σ v) hΩ hne
      (hg.mono Set.inter_subset_left) hrank
    have himg : (σ '' {t | t ∈ Ω ∧ A *ᵥ σ t = y}).Infinite :=
      hy.image (hinj.mono fun t ht => ht.1.1)
    have hfin := (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
    refine himg (hfin.subset ?_)
    rintro x ⟨t, ⟨⟨htb, htN⟩, hty⟩, rfl⟩
    exact ⟨hZ t htb htN, hty⟩

  have han : AnalyticOnNhd ℂ (fun w =>
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ))
      (ball (0 : Fin d → ℂ) r) := fun w hw =>
    IndefiniteRowSideFullHecke.ComplexSets.analyticAt_det_fderiv
      (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.analyticAt_of_differentiableOn isOpen_ball hg hw)
  refine measure_mono_null ?_ (ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball
    (convex_ball (0 : Fin d → ℂ) r).isPreconnected han hsome)
  exact fun w hw => ⟨hw.1, hw.2.2⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamPieceInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace ParamPieceInt

theorem analyticAt_of_differentiableOn {d m : ℕ} {U : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin d → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

variable {n d : ℕ}

theorem differentiable_mulVec (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
  have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
  convert h using 1
  ext x
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]

theorem exists_sheet {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {σ : (Fin d → ℂ) → Fin n → ℂ} {r r' : ℝ} {N : Set (Fin n → ℂ)}
    (hσ : DifferentiableOn ℂ σ (Metric.ball 0 r)) (hinj : Set.InjOn σ (Metric.ball 0 r))
    (hN : IsOpen N) (hrr : r' < r)
    (hprop : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r')
    (hcov : zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r)
    {w : Fin d → ℂ} (hw : w ∈ Metric.ball 0 r) (hwN : σ w ∈ N)
    (hdet : LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) :
    ∃ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt W A (σ w) s ∧
      ∀ᶠ v in 𝓝 w, s (A *ᵥ σ v) = σ v := by
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hstrict : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) w := by
    have he : (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g w := by
      ext1 v
      simp
    rw [he]
    exact (hgan w hw).hasStrictFDerivAt
  obtain ⟨e, heg, hwe⟩ : ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ),
      (e : (Fin d → ℂ) → Fin d → ℂ) = g ∧ w ∈ e.source :=
    ⟨hstrict.toOpenPartialHomeomorph g, hstrict.toOpenPartialHomeomorph_coe,
      hstrict.mem_toOpenPartialHomeomorph_source⟩

  have hdetc : ContinuousAt (fun v => (fderiv ℂ g v).det) w :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (hgan w hw).fderiv.continuousAt
  have h1 : ∀ᶠ v in 𝓝 w, v ∈ Ω := hΩo.mem_nhds ⟨hw, hwN⟩
  have h2 : ∀ᶠ v in 𝓝 w, v ∈ e.source := e.open_source.mem_nhds hwe
  have hev : ∀ᶠ v in 𝓝 w, (v ∈ Ω ∧ v ∈ e.source) ∧ (fderiv ℂ g v).det ≠ 0 :=
    (h1.and h2).and (hdetc.eventually_ne hdet)
  obtain ⟨O, hOp, hOo, hwO⟩ := eventually_nhds_iff.1 hev
  have hsymm : ∀ v ∈ O, e.symm (g v) = v := fun v hv => by
    rw [← heg]; exact e.left_inv (hOp v hv).1.2
  set U : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' O with hU
  have hUo : IsOpen U := e.isOpen_inter_preimage_symm hOo
  have hgU : ∀ v ∈ O, g v ∈ U := fun v hv =>
    ⟨by rw [← heg]; exact e.map_source (hOp v hv).1.2, by
      show e.symm (g v) ∈ O; rw [hsymm v hv]; exact hv⟩
  have hright : ∀ y ∈ U, g (e.symm y) = y := fun y hy => by
    rw [← heg]; exact e.right_inv hy.1
  have hsymmd : ∀ y ∈ U, DifferentiableAt ℂ e.symm y := by
    intro y hy
    have hv : e.symm y ∈ O := hy.2
    have hd := (hOp _ hv).2
    have hf : HasFDerivAt (e : (Fin d → ℂ) → Fin d → ℂ)
        (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) (e.symm y) := by
      have he : (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g (e.symm y) := by
        ext1 v
        simp
      rw [he, heg]
      exact (hgan _ (hOp _ hv).1.1.1).differentiableAt.hasFDerivAt
    exact (e.hasFDerivAt_symm hy.1 hf).differentiableAt
  refine ⟨σ ∘ e.symm, ⟨U, hUo, hgU w hwO, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    exact ((hσ.differentiableAt (Metric.isOpen_ball.mem_nhds (hOp _ hv).1.1.1)).comp y
      (hsymmd y hy)).differentiableWithinAt
  · show σ (e.symm (g w)) = σ w
    rw [hsymm w hwO]
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    refine ⟨hright y hy, ?_⟩
    exact (hprop _ (hOp _ hv).1.1.1 (hOp _ hv).1.1.2).1
  ·
    set K : Set (Fin d → ℂ) := Metric.closedBall 0 r' \ O with hK
    have hKb : K ⊆ Metric.ball 0 r := fun v hv => Metric.closedBall_subset_ball hrr hv.1
    have hKc : IsCompact (σ '' K) :=
      ((isCompact_closedBall 0 r').diff hOo).image_of_continuousOn (hσ.continuousOn.mono hKb)
    have hwK : σ w ∉ σ '' K := by
      rintro ⟨k, hk, hkw⟩
      exact hk.2 (hinj (hKb hk) hw hkw ▸ hwO)
    refine ⟨N ∩ (σ '' K)ᶜ, (hN.inter hKc.isClosed.isOpen_compl).mem_nhds ⟨hwN, hwK⟩, ?_⟩
    rintro x' ⟨hx'Z, hx'N, hx'K⟩ -
    obtain ⟨v, hvb, rfl⟩ := hcov ⟨hx'Z, hx'N⟩
    have hvr : ‖v‖ ≤ r' := (hprop v hvb hx'N).2
    have hvO : v ∈ O := by
      by_contra hvO
      exact hx'K ⟨v, ⟨mem_closedBall_zero_iff.2 hvr, hvO⟩, rfl⟩
    show σ v = σ (e.symm (g v))
    rw [hsymm v hvO]
  · filter_upwards [hOo.mem_nhds hwO] with v hv
    show σ (e.symm (g v)) = σ v
    rw [hsymm v hv]

end ParamPieceInt


open ParamPieceInt in
theorem ParamPieceInt.proof : ParamPieceInt.Statement := by
  intro n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ P hφ hPm hPb hPw hgP
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hdens : ∀ w ∈ P, Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det *
      chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w := by
    intro w hw
    obtain ⟨s, hs, hsg⟩ := exists_sheet hσ hinj hN hrr hprop hcov (hPb hw) (hPw w hw).1 (hPw w hw).2
    have hex : ∃ s, IsSheetAt W A (σ w) s := ⟨s, hs⟩
    have hfib : σ w ∈ fibre W A (g w) := ⟨(hprop w (hPb hw) (hPw w hw).1).1, rfl⟩
    have hsum : chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) := by
      unfold chartDens sheetSum
      rw [finsum_eq_single _ (σ w), finsum_eq_if, if_pos hfib, dite_eq_left hex]
      · beta_reduce
        rw [Set.indicator_of_mem (Set.mem_image_of_mem σ hw), IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
          (SheetSumMeasurable.sheet_eventuallyEq hs hex.choose_spec).fun_comp (φ k)]
      · intro x hxne
        rw [finsum_eq_if]
        split_ifs with hx h
        · beta_reduce
          rw [Set.indicator_of_notMem, zero_mul]
          rintro ⟨w', hw', rfl⟩
          exact hxne (by rw [hgP hw' hw hx.2])
        · rfl
        · rfl

    obtain ⟨U, hUo, hwU, hsd, hsx, -, -⟩ := hs
    have hsc : ContDiffAt ℝ 2 s (g w) :=
      (analyticAt_of_differentiableOn hUo hsd hwU).contDiffAt.restrict_scalars ℝ
    have hφs : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (g w) := by
      intro k
      obtain ⟨Uk, hUko, hZU, hcd⟩ := hφ k
      have hmem : s (g w) ∈ Uk := by
        show s (A *ᵥ σ w) ∈ Uk
        rw [hsx]; exact hZU (hprop w (hPb hw) (hPw w hw).1).1
      exact ((hcd.contDiffAt (hUko.mem_nhds hmem)).of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp (g w) hsc
    have hcomp : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w =
        ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) g w (hgan w (hPb hw)) hφs
    have hev : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w =
        ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w :=
      IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
        filter_upwards [hsg] with v hv
        simp only [Function.comp_apply, g]
        rw [hv]
    rw [hsum, hev, hcomp]
    ring

  have hzero : ∀ y, y ∉ g '' P → chartDens W A ((σ '' P).indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · beta_reduce
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨w, hw, rfl⟩
      exact hy ⟨w, hw, hx.2⟩
    · rfl
  have hgdP : ∀ w ∈ P, DifferentiableAt ℂ g w := fun w hw => (hgan w (hPb hw)).differentiableAt
  unfold chartInt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_image_eq_integral_abs_det_fderiv_smul volume hPm
      (fun x hx => ((hgdP x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hgP]
  refine setIntegral_congr_fun hPm fun w hw => ?_
  rw [ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq g w (hgdP w hw),
    abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul, hdens w hw]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PosPartLocal

variable {n d : ℕ}

theorem chartPosDens_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : IsOpen W) (hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartPosDens J A (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold chartPosDens sheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hfib : s y ∈ fibre J A y := ⟨(hsec y hy.1).2, (hsec y hy.1).1⟩
    have hsh : IsSheetAt J A (s y) s :=
      ⟨U, hU, by rw [(hsec y hy.1).1]; exact hy.1, hsd, by rw [(hsec y hy.1).1], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ => (hWs x' hx').2.symm⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dite_eq_left ⟨s, hsh⟩]
    · have h := SheetSumMeasurable.term_eq (fun a b => max (a * b) 0) (E.indicator f) φ hsh ⟨s, hsh⟩
      rw [(hsec y hy.1).1] at h
      dsimp only
      rw [h, Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2
          rw [hx.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl

end PosPartLocal

theorem PosPartLocal.proof : PosPartLocal.Statement := by
  rintro n d J A A' f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', -, hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hAc' : Continuous fun z : Fin n → ℂ => A' *ᵥ z := by fun_prop
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (fun z => A' *ᵥ z) ⁻¹' U')
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter (hU'.preimage hAc'))
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W, A' *ᵥ x' ∈ U' ∧ s' (A' *ᵥ x') = x' :=
    by rintro x' ⟨hZ, -, ⟨hV1, hU1⟩⟩; exact ⟨hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    PosPartLocal.chartPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).2, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).1, ← (hsec' z₂ h₂.1).1, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨A' *ᵥ s y, ⟨(hWs' _ hZ).1, ?_⟩, ?_⟩
        · show s' (A' *ᵥ s y) ∈ W
          rw [(hWs' _ hZ).2]
          exact hZ.2
        · show A *ᵥ s' (A' *ᵥ s y) = y
          rw [(hWs' _ hZ).2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).2)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormFullRootFactor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormFullRootFactor.proof (hWin : PrimitiveFormWindow.Statement)
    (hBr : AnalyticRootBranch.Statement) (hConst : PrimitiveFormFullBranchConstant.Statement)
    (hFac : PolynomialRootPredicateFactor.Statement) : PrimitiveFormFullRootFactor.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδne hP hsep hQ
  obtain ⟨W, B, N', k, f, hWo, hwW, hBo, hBc, hAwB, hN'o, hcl, hf, hXN, hsph, hPW, -, haB, hδB, hqB,
    hsepB⟩ := hWin σ X w d A hX hiso ℓ N a δ q ha hδ hq hP hsep hQ
  have hex : ∃ t ∈ B, δ t ≠ 0 := by
    by_contra h
    push Not at h
    exact hδne (Filter.mem_of_superset (hBo.mem_nhds hAwB) h)
  have hloc : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧
          (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q t₀ τ₀) := by
    intro t₀ ht₀ hδt₀ τ₀ hτ₀
    obtain ⟨O, r, hOo, ht₀O, hr, hrt₀, hroot⟩ :=
      hBr d N a t₀ τ₀ (fun j => haB j t₀ ht₀) (hsepB t₀ ht₀ hδt₀) hτ₀
    have hU : IsOpen (O ∩ (B ∩ δ ⁻¹' {0}ᶜ)) :=
      hOo.inter (hδB.continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t₀ ⟨ht₀O, ht₀, hδt₀⟩
    have hsub : ∀ s ∈ Metric.ball t₀ ε, s ∈ O ∧ s ∈ B ∧ δ s ≠ 0 := fun s hs =>
      ⟨(hball hs).1, (hball hs).2.1, (hball hs).2.2⟩
    have hc := hConst σ X W N' k f d A ℓ N a δ q B (Metric.ball t₀ ε) r hWo hN'o hcl hf hXN hsph hPW hBo
      haB hδB hqB Metric.isOpen_ball (convex_ball t₀ ε).isPreconnected (fun s hs => (hsub s hs).2.1)
      (fun s hs => (hsub s hs).2.2) (fun s hs => hsepB s (hsub s hs).2.1 (hsub s hs).2.2)
      (hr.mono fun s hs => (hsub s hs).1) (fun s hs => hroot s (hsub s hs).1)
    refine ⟨Metric.ball t₀ ε, r, Metric.isOpen_ball, Metric.mem_ball_self hε,
      hr.continuousOn.mono fun s hs => (hsub s hs).1, hrt₀, fun s hs => ⟨hroot s (hsub s hs).1, ?_⟩⟩
    rw [← hrt₀]
    exact hc s hs t₀ (Metric.mem_ball_self hε)
  obtain ⟨C, E, hCE, hprod, hzero⟩ :=
    hFac d N B a δ (PrimitiveFormRootFull X W A ℓ δ q) hBo hBc haB hδB hex hsepB hloc
  exact ⟨W, B, C, E, hWo, hwW, hBo, hAwB, hCE, hprod, hzero⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

