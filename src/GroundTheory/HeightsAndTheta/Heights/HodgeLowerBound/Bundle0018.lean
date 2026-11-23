module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BdPtsNull.proof (h : ParamImageNull.Statement) : BdPtsNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  refine h K ι (mCoordIdeal D.y) D.n D.nCharts (fun _ => Metric.ball 0 1)
    (fun a => {t | t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 ∧ ∃ i : Fin D.n, (i : ℕ) < (D.chart a).a ∧ t i = 0})
    (fun a => (D.chart a).γ) D.Bd (fun _ => Metric.isOpen_ball) (fun _ _ ht => ht.1) ?_
    (fun a => (D.chart a).analytic) ?_
  · intro a
    refine measure_mono_null (t := ⋃ i : Fin D.n, {t : Fin D.n → ℂ | t i = 0}) ?_
      (measure_iUnion_null fun i => ?_)
    · rintro t ⟨-, i, -, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · rw [volume_pi]
      exact Measure.pi_hyperplane _ i 0
  · rintro z ⟨hz, -⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z (D.bd_subset hz)
    have htb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt ht (by norm_num))
    have hγ : (D.chart a).γ t ∈ D.Bd := by
      have h' := D.bd_torus _ hz c⁻¹ (fun k => inv_ne_zero (hc k))
      convert h' using 1
      funext p
      simp [torusSmul, hc p.1]
    exact ⟨a, t, ⟨htb, ((D.chart a).boundary t htb).1 hγ⟩, c, hc, rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryPtsNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : segre (torusSmul c z) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem volume_coord_hyperplane {m : ℕ} (i : Fin m) : volume {t : Fin m → ℂ | t i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

theorem differentiable_segre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    Differentiable ℂ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
  refine differentiable_pi.2 fun i => ?_
  unfold segre
  fun_prop

theorem BoundaryPtsNull.proof : BoundaryPtsNull.Statement := by
  intro II T _ _ K _ ι _ Ω _ _ E _ _ D Ψ _
  classical
  let F : Fin D.nCharts → (Fin D.n → ℂ) → Fin D.n → ℂ := fun a t j =>
    Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0
  let s : Fin D.nCharts → Fin D.n → Set (Fin D.n → ℂ) := fun a i =>
    {t | ‖t‖ < 1 ∧ t i = 0 ∧ Ψ (segre ((D.chart a).γ t)) 0 ≠ 0}
  refine measure_mono_null (t := ⋃ a, ⋃ i, F a '' s a i) ?_
    (measure_iUnion_null fun a => measure_iUnion_null fun i => ?_)
  · rintro y ⟨z, hz, hzB, hΨ⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z hz
    have hγB : (D.chart a).γ t ∈ D.Bd := by
      have := D.bd_torus _ hzB (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))
      convert this using 1
      funext x
      simp [torusSmul, hc]
    have ht1 : ‖t‖ < 1 := by linarith
    obtain ⟨i, -, hi⟩ := ((D.chart a).boundary t (mem_ball_zero_iff.2 ht1)).1 hγB
    rw [segre_torusSmul, map_smul] at hΨ
    have h0 := congrFun hΨ 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hv0 : Ψ (segre ((D.chart a).γ t)) 0 ≠ 0 := fun h => by simp [h] at h0
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨i, t, ⟨ht1, hi, hv0⟩, ?_⟩⟩
    funext j
    have hj := congrFun hΨ j.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hj
    show Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0 = y j
    rw [div_eq_iff hv0, ← hj]
    linear_combination (-(Ψ (segre ((D.chart a).γ t)) j.succ)) * h0
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (fun t ht => ht.2.1) (volume_coord_hyperplane i))
    intro t ht
    have hγ : DifferentiableAt ℂ (D.chart a).γ t :=
      ((D.chart a).analytic t (mem_ball_zero_iff.2 ht.1)).differentiableAt
    have hS : DifferentiableAt ℂ (fun t => segre ((D.chart a).γ t)) t := by
      have := differentiable_segre.differentiableAt.comp t hγ
      exact this
    have hG : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t))) t := by
      have := (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp t hS
      exact this
    have hF : DifferentiableAt ℂ (F a) t := by
      refine differentiableAt_pi.2 fun j => ?_
      have hn : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) j.succ) t :=
        differentiableAt_pi.1 hG j.succ
      have hd : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) 0) t :=
        differentiableAt_pi.1 hG 0
      show DifferentiableAt ℂ
        (fun t => Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0) t
      simp only [div_eq_mul_inv]
      exact hn.mul (hd.inv ht.2.2)
    exact (hF.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set
open ReciprocityTheory.AnForm.A (coordDiv)

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact measure_iUnion_null fun i => measure_iUnion_null fun _ =>
    Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton 0)

theorem DivisorPreimageNull.proof (h : ParamImageNull.Statement) : DivisorPreimageNull.Statement := by
  intro K _ ι _ P d M R
  classical
  have hloc : ∀ x : M.Xc, ∃ W : Set M.Xc, IsOpen W ∧ x ∈ W ∧ ∃ j : Fin R.N, W ⊆ (R.chart j).source ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y ∈ W, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn W fun y => s y p := by
    intro x
    obtain ⟨U, hU, hxU, s, hs, hhol⟩ := M.sections x
    obtain ⟨j, hj⟩ := R.cover x
    refine ⟨U ∩ (R.chart j).source, hU.inter (R.chart j).open_source,
      ⟨hxU, R.mid_subset_source j (R.inner_subset_mid j hj)⟩, j, inter_subset_right, s,
      fun y hy => hs y hy.1, fun p i => ?_⟩
    exact (hhol p i).mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))
  choose W hWo hxW j hWj s hs hhol using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  let xs : Fin t.card → M.Xc := fun i => (t.equivFin.symm i : M.Xc)
  refine h K ι P d t.card (fun i => R.chart (j (xs i)) '' W (xs i))
    (fun i => R.chart (j (xs i)) '' W (xs i) ∩ coordDiv (R.S (j (xs i))))
    (fun i w => s (xs i) ((R.chart (j (xs i))).symm w)) {z | M.proj z ∉ R.Yo}
    (fun i => (R.chart (j (xs i))).isOpen_image_of_subset_source (hWo _) (hWj _))
    (fun i => inter_subset_left)
    (fun i => measure_mono_null inter_subset_right (volume_coordDiv _)) ?_ ?_
  · rintro i w ⟨y, hyW, rfl⟩
    refine analyticAt_pi_iff.2 fun p => ?_
    exact GroundTheory.Heights₂.Heights.Regular.analyticAt_comp_symm_of_holoOn (R.compat _) (hhol (xs i) p) hyW
      (hWj _ hyW)
  · rintro z ⟨hzY, hz⟩
    obtain ⟨x, hxt, hzW⟩ := mem_iUnion₂.1 (ht (mem_univ (M.proj z)))
    obtain ⟨i, rfl⟩ : ∃ i, xs i = x := ⟨t.equivFin ⟨x, hxt⟩, by simp [xs]⟩
    have hsrc := hWj (xs i) hzW
    have hdiv : R.chart (j (xs i)) (M.proj z) ∈ coordDiv (R.S (j (xs i))) := by
      by_contra hc
      exact hzY ((R.mem_Yo _ _ hsrc).2 hc)
    refine ⟨i, R.chart (j (xs i)) (M.proj z), ⟨⟨M.proj z, hzW, rfl⟩, hdiv⟩, ?_⟩
    have hγ : s (xs i) ((R.chart (j (xs i))).symm (R.chart (j (xs i)) (M.proj z))) = s (xs i) (M.proj z) := by
      rw [(R.chart (j (xs i))).left_inv hsrc]
    rw [hγ]
    obtain ⟨hsm, hsp⟩ := hs (xs i) (M.proj z) hzW
    exact (M.fibre _ hsm z hz).1 hsp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioFieldEq.proof (h₁ : RatioFieldSpan.Statement) (h₂ : HodgeFlagSpan.Statement)
    (h₃ : PivotMinorFlag.Statement) (h₄ : GenLeadMinor0NeZero.Statement) : HodgeFlagRatioFieldEq.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc

  have hq : ∀ (τ : Ψ) (i : Fin (D.N - 1)),
      IntermediateField.adjoin Ω (Set.range fun m =>
          Pl.pluecker0 B τ i m / Pl.pluecker0 B τ i (c (Sum.inr (τ, i)))) =
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) := by
    intro τ i
    have hspan := h₂ II Ψ K ι Ω E D Pl H B τ i
    obtain ⟨S₀, hS₀⟩ := h₃ _ D.N (genMat0Fr Ω Ψ D.N D.j τ) i (Fin.castLE (Nat.sub_le D.N 1) i) le_rfl
    refine h₁ Ω Pl.ΩY _ _ _ _ _ _ hspan (Submodule.subset_span ⟨_, rfl⟩) ?_ (hc (Sum.inr (τ, i)))
      (h₄ Ω Ψ D.N D.j τ i)
    rw [hspan]
    exact Submodule.subset_span ⟨S₀, by rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor, hS₀]⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | q, t⟩, rfl⟩
    · show Pl.ofΩ (D.y ⟨k, t⟩) / Pl.ofΩ (D.y ⟨k, c (Sum.inl k)⟩) ∈ _
      rw [PlueckerData.ofΩ_eq, PlueckerData.ofΩ_eq, ← map_div₀]
      exact IntermediateField.algebraMap_mem _ _
    · have hmem : Pl.pluecker0 B q.1 q.2 t / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2))) ∈
          IntermediateField.adjoin Ω (Set.range fun m =>
            Pl.pluecker0 B q.1 q.2 m / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2)))) :=
        IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩
      rw [hq] at hmem
      refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
      rintro _ ⟨S, rfl⟩
      exact ⟨(q.1, ⟨q.2, S⟩), rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨τ, i, S⟩, rfl⟩
    have hmem : flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i ∈
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) :=
      IntermediateField.subset_adjoin _ _ ⟨S, rfl⟩
    rw [← hq] at hmem
    refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨Sum.inr (τ, i), m⟩, rfl⟩

theorem HodgeFlagRatioFieldEq.full : HodgeFlagRatioFieldEq.Statement :=
  HodgeFlagRatioFieldEq.proof RatioFieldSpan.full HodgeFlagSpan.full PivotMinorFlag.full GenLeadMinor0NeZero.full

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem maDensity_const_nonneg {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hφ : ContDiffAt ℝ 2 φ y)
    (hL : ∀ v, 0 ≤ leviForm φ y v) : 0 ≤ maDensity (fun _ : Fin D => φ) y := by
  unfold maDensity
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mixedDiscriminant_constant]
  have hS : IsSymmSndFDerivAt ℝ φ y := hφ.isSymmSndFDerivAt (by simp)
  have hP := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.complexHessian_posSemidef hS (zero_le_one' ℝ) hL
  have hd := hP.det_nonneg
  rw [Complex.ofReal_one, one_smul, Matrix.det_transpose] at hd
  have hre : 0 ≤ (cxHessian φ y).det.re := (Complex.nonneg_iff.1 hd).1
  have h1 : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D := by positivity
  exact mul_nonneg h1 hre

theorem MuHomDensityNonneg.proof (h : MuSheetLeviNonneg.Statement) : MuHomDensityNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q hQ
  filter_upwards [h II Ψ K ι Ω E D O Lt X Q hQ] with y hy w
  unfold sheetDensity
  split_ifs with hγ
  · obtain ⟨h2, hL⟩ := hy w _ hγ.choose_spec
    rw [one_mul]
    exact maDensity_const_nonneg h2 hL
  · exact le_rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric Set

namespace MuRegSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothAlong_mul {S : Set ((Σ k, ι k) → ℂ)} {f g : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f)
    (hg : SmoothAlong S g) : SmoothAlong S fun z => f z * g z := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  obtain ⟨V, hV, G, hG, hgG⟩ := hg z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, fun w => F w * G w,
    (hF.mono inter_subset_left).mul (hG.mono inter_subset_right), fun w hw => ?_⟩
  show f w * g w = F w * G w
  rw [hfF w ⟨hw.1.1, hw.2⟩, hgG w ⟨hw.1.2, hw.2⟩]

theorem smoothAlong_prod {S : Set ((Σ k, ι k) → ℂ)} {α : Type} (s : Finset α)
    {f : α → ((Σ k, ι k) → ℂ) → ℝ} (hf : ∀ p ∈ s, SmoothAlong S (f p)) :
    SmoothAlong S fun z => ∏ p ∈ s, f p z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z _
    exact ⟨univ, univ_mem, fun _ => 1, contDiffOn_const, fun w _ => by simp⟩
  | insert a s ha ih =>
    have h := smoothAlong_mul (hf a (Finset.mem_insert_self a s))
      (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))
    intro z hz
    obtain ⟨U, hU, G, hG, hfG⟩ := h z hz
    exact ⟨U, hU, G, hG, fun w hw => by
      show ∏ p ∈ insert a s, f p w = G w
      rw [Finset.prod_insert ha]; exact hfG w hw⟩

theorem smoothAlong_exp {S : Set ((Σ k, ι k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f) :
    SmoothAlong S fun z => Real.exp (f z) := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  exact ⟨U, hU, fun w => Real.exp (F w), Real.contDiff_exp.comp_contDiffOn hF,
    fun w hw => by show Real.exp (f w) = Real.exp (F w); rw [hfF w hw]⟩


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smoothAlong_of_contDiffOn {P : Ideal (MRing ι)} {f : ((Σ k, ι k) → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) : SmoothAlong (mcPts P) f :=
  fun _ hz => ⟨_, isOpen_blocks.mem_nhds hz.1, f, hf, fun _ _ => rfl⟩

theorem regWeight_smooth {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) := by
  have hball : ∀ j, ∃ δ : ℝ, 0 < δ ∧
      cthickening δ (S.R.chart j '' closure (S.R.mid j)) ⊆ (S.R.chart j).target := by
    intro j
    have hK : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
      isClosed_closure.isCompact.image_of_continuousOn
        ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
    have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target :=
      image_subset_iff.2 fun x hx => (S.R.chart j).map_source (S.R.closure_mid j hx)
    exact hK.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  choose δ hδ hδs using hball
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, t < δ j :=
    Filter.eventually_all.2 fun j => nhdsWithin_le_nhds (gt_mem_nhds (hδ j))
  filter_upwards [hev, hS.compare, self_mem_nhdsWithin] with t htδ hcmp ht
  have ht0 : (0 : ℝ) < t := ht
  exact (Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht0
    (ht0.trans_le (S.e1_ge t ht0))
    (fun j x hx => ((closedBall_subset_closedBall (htδ j).le).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) _)).trans (hδs j)) hcmp).1

theorem prod_norm_zpow_add_sum {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) (s : Finset ℕ) (b : ℕ → K → ℤ) :
    (∏ k, ‖c k‖ ^ (a + ∑ p ∈ s, b p) k) = (∏ k, ‖c k‖ ^ a k) * ∏ p ∈ s, ∏ k, ‖c k‖ ^ b p k := by
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  have hsum : ∀ s' : Finset ℕ, ‖c k‖ ^ (∑ p ∈ s', b p k) = ∏ p ∈ s', ‖c k‖ ^ b p k := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => simp
    | insert q s' hq ih => rw [Finset.sum_insert hq, Finset.prod_insert hq, zpow_add₀ h0, ih]
  rw [Pi.add_apply, Finset.sum_apply, zpow_add₀ h0, hsum]

end MuRegSmooth


open MuRegSmooth TopNPoly in
theorem MuRegSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (hVS : VertFactorSmooth.Statement) (hV : VertFactorPos.Statement) : MuRegSmooth.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B
  filter_upwards [regWeight_smooth X.S X.S_tied] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _))
      (Finset.prod_pos fun p hp => hV II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz)
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z :=
      ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, X.S.ref.smul c z hc, X.S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp =>
        (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι (mCoordIdeal D.y) (muTwDeg X.H B) F hPm hpos hhom hsm
  unfold muReg
  refine smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => ?_
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hw0 := orbitRep_blocks hz.1
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz.1 hG0
  have hFw : (X.S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
    rw [hreg]
  rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
  conv_lhs => rw [hzc]
  exact hhom _ hwP c hc

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PushDown.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hStep : Inter.PFStep.Statement)
    (hArith : HodgeFlagArith.Statement) : PushDown.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  have hPF := Inter.PushforwardProjLineFlag.proof hAI3 hStep
  have hY := hArith II Ψ K ι Ω E D Pl H B
  have hX : IsArithVar (imageZ Pl.xV (Pl.flagPrime B)) (D.n + 1) := by
    rw [Pl.imageZ_forget_flagPrime]
    exact D.arith
  refine ⟨fun G J L L' N hJ hL hL' hN => ?_, fun d r L L' N hdr hd hL hL' hN => ?_⟩
  · have h := hPF II hII.1 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) D.flagDim0
      G J L L' N Pl.isBlockMap_xV hY hX hJ hL hL' hN
    rwa [Pl.imageZ_forget_flagPrime] at h
  · exact hII.2.2.2 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) d r L L' N
      Pl.isBlockMap_xV (by rw [hdr]; exact hY) hX hd hL hL' hN

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

