module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem val_chart_symm_apply {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) {w : V n} (hw : w ∈ e.target) : ((e.symm w : U) : V n) = w := by
  have h1 : e.symm w ∈ e.source := e.map_target hw
  rw [he h1]
  exact e.right_inv hw

private theorem comp_chart_symm_eventuallyEq_of_mem_target {n : ℕ} {U : Set (V n)} (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n Subtype.val e) (g : V n → ℂ) {w : V n} (hw : w ∈ e.target) :
    (fun y : U => g y.1) ∘ e.symm =ᶠ[nhds w] g := by
  filter_upwards [e.open_target.mem_nhds hw] with y hy
  simp only [Function.comp_apply]
  rw [val_chart_symm_apply e he hy]

private theorem exists_isChart_subtype_val {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (y : U) : ∃ e : OpenPartialHomeomorph U (V n), IsChart n Subtype.val e ∧ y ∈ e.source := by
  obtain ⟨e, hy, he⟩ := hz y
  exact ⟨e, fun a _ => by rw [he], hy⟩

private theorem db_subtype_val_eq_wdb {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : db n Subtype.val k (fun y : U => g y.1) y = wdb n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold db
  rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wdb
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

private theorem d_subtype_val_eq_wd {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (g : V n → ℂ) (k : Fin n) (y : U) : d n Subtype.val k (fun y : U => g y.1) y = wd n k g y.1 := by
  have hex := exists_isChart_subtype_val hz y
  unfold d
  rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  have hw : y.1 ∈ (Classical.choose hex).target := by
    rw [hc.1 hc.2]
    exact (Classical.choose hex).map_source hc.2
  unfold wd
  rw [(comp_chart_symm_eventuallyEq_of_mem_target _ hc.1 g hw).fderiv_eq]

private theorem levi_lemma_6 {n : ℕ} {U : Set (V n)} (hz : IsLocalHomeomorph (Subtype.val : U → V n))
    (ph : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n Subtype.val (fun y : U => ph y.1) x ξ = leviV n (fun w => ((ph w : ℝ) : ℂ)) x.1 ξ := by
  unfold Levi leviV
  beta_reduce
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h1 : db n Subtype.val k (fun y : U => ((ph y.1 : ℝ) : ℂ)) =
      fun y : U => wdb n k (fun w => ((ph w : ℝ) : ℂ)) y.1 :=
    funext fun y => db_subtype_val_eq_wdb hz (fun w => ((ph w : ℝ) : ℂ)) k y
  rw [h1, d_subtype_val_eq_wd hz (wdb n k (fun w => ((ph w : ℝ) : ℂ))) j x]

private theorem leviV_add {n : ℕ} (g1 g2 : V n → ℂ) (y : V n)
    (h1 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g1 w) (h2 : ∀ᶠ w in nhds y, ContDiffAt ℝ ∞ g2 w)
    (ξ : Fin n → ℂ) :
    leviV n (fun w => g1 w + g2 w) y ξ = leviV n g1 y ξ + leviV n g2 y ξ := by
  have hev : ∀ k, wdb n k (fun w => g1 w + g2 w) =ᶠ[nhds y] fun w => wdb n k g1 w + wdb n k g2 w := by
    intro k
    filter_upwards [h1, h2] with w hw1 hw2
    have d1 : DifferentiableAt ℝ g1 w := hw1.differentiableAt (by first | norm_num | simp)
    have d2 : DifferentiableAt ℝ g2 w := hw2.differentiableAt (by first | norm_num | simp)
    unfold wdb
    first
      | rw [fderiv_fun_add d1 d2]
      | rw [fderiv_add' d1 d2]
      | rw [show (fun w => g1 w + g2 w) = g1 + g2 from rfl, fderiv_add d1 d2]
    simp only [ContinuousLinearMap.add_apply]
    ring
  have hdiff : ∀ g : V n → ℂ, ContDiffAt ℝ ∞ g y → ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro g hg k
    have hf : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by
      first
        | exact WithTop.coe_le_coe.mpr le_top
        | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
        | (norm_num; done)
        | (simp; done))
    have hfd : DifferentiableAt ℝ (fderiv ℝ g) y := hf.differentiableAt (by first | exact one_ne_zero | exact le_rfl | simp)
    have ha : DifferentiableAt ℝ (fun w => fderiv ℝ g w (bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    have hb : DifferentiableAt ℝ (fun w => fderiv ℝ g w (Complex.I • bas n k)) y :=
      hfd.clm_apply (differentiableAt_const _)
    unfold wdb
    first
      | exact (ha.fun_add (hb.const_mul Complex.I)).div_const 2
      | exact (ha.add (hb.const_mul Complex.I)).div_const 2
      | fun_prop
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : wd n j (wdb n k (fun w => g1 w + g2 w)) y =
      wd n j (wdb n k g1) y + wd n j (wdb n k g2) y := by
    unfold wd
    rw [(hev k).fderiv_eq]
    first
      | rw [fderiv_fun_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
      | rw [fderiv_add' (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
      | rw [show (fun w => wdb n k g1 w + wdb n k g2 w) = wdb n k g1 + wdb n k g2 from rfl,
          fderiv_add (hdiff g1 h1.self_of_nhds k) (hdiff g2 h2.self_of_nhds k)]
    simp only [ContinuousLinearMap.add_apply]
    ring
  rw [e1]
  ring

theorem exhaustF_holds : ExhaustFStatement (E := E) := by
  intro r X x0 ho
  have hU : IsOpen (OmF X x0) := ExF.isOpen_OmF X x0
  have hz : IsLocalHomeomorph (Subtype.val : OmF X x0 → _) := by
    first
      | exact hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      | exact hU.openEmbedding_subtype_val.isLocalHomeomorph
  have hgE : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((eF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.eF_contDiffAt X x0 ho hw)
  have hg1 : ∀ w ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w := fun w hw =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (ExF.rhF_contDiffAt X x0 ho hw)
  have hg2 : ∀ {m : ℕ} (w : V m), ContDiffAt ℝ ∞ (fun w : V m => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
    fun w => Complex.ofRealCLM.contDiff.contDiffAt.comp w
      ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun w => by positivity).contDiffAt
  refine ⟨{
      z := Subtype.val
      isLocalHomeomorph := hz
      e := (fun y => eF X x0 y.1)
      smooth_e := ?_
      levi_e := ?_
      isCompact_le := ?_ }, rfl, rfl⟩
  · unfold SmoothR Smooth
    intro e he
    refine ContDiffOn.congr (f := fun w => ((eF X x0 w : ℝ) : ℂ))
      (fun w hw => (hgE w ?_).contDiffWithinAt) (fun w hw => ?_)
    · rw [← val_chart_symm_apply e he hw]
      exact (e.symm w).2
    · simp only [Function.comp_apply]
      rw [val_chart_symm_apply e he hw]
  · unfold LeviNonneg
    intro x ξ
    rw [levi_lemma_6 hz (eF X x0) x ξ]
    have hsplit : (fun w => ((eF X x0 w : ℝ) : ℂ)) =
        fun w => ((rhF X x0 w : ℝ) : ℂ) + ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := by
      funext w
      simp [eF]
    have hev1 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w :=
      Filter.eventually_of_mem (hU.mem_nhds x.2) hg1
    have hev2 : ∀ᶠ w in nhds x.1, ContDiffAt ℝ ∞ (fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ)) w :=
      Filter.Eventually.of_forall fun w => hg2 w
    rw [hsplit, leviV_add _ _ _ hev1 hev2, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho x.2 ξ) (ExF.leviT_nonneg _ ξ)
  · intro a
    have hc := ExF.isCompact_subF X x0 ho a
    rw [Subtype.isCompact_iff]
    convert hc using 1
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hw, ha⟩
      exact ⟨⟨w, hw⟩, ha, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

local instance instMSMat {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelMat {m n : Type*} [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

theorem meas_inv {n : Type*} [Fintype n] [DecidableEq n] : Measurable fun A : Matrix n n ℂ => A⁻¹ := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

theorem meas_Yb {p q : ℕ} : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => Yb M := by
  have hB : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => M.toBlocks₂₂ :=
    (show Continuous fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
        (M.toBlocks₂₂ : Matrix (Fin q) (Fin q) ℂ) from
      continuous_pi fun i => continuous_pi fun j =>
        continuous_id.matrix_elem (Sum.inr i) (Sum.inr j)).measurable
  have hBi := (meas_inv (n := Fin q)).comp hB
  unfold Yb
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (continuous_id.matrix_elem (Sum.inl i) (Sum.inr k)).measurable.mul
    ((continuous_id.matrix_elem k j).measurable.comp hBi)

theorem meas_dpow {p q : ℕ} (s : ℝ) : Measurable fun Z : Matrix (Fin p) (Fin q) ℂ => dpow Z s := by
  unfold dpow
  exact (Complex.continuous_re.comp ((continuous_const.sub
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)).matrix_det)).measurable.pow_const s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cont_mat (X : Data E r) (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ

theorem cont_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) : Continuous fun x => Mx X x0 x τ := by
  unfold Mx tl
  exact (continuous_const.matrix_mul (cont_mat X τ)).matrix_submatrix _ _

theorem meas_kap (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kap X x0 bb) := by
  unfold kap
  exact Finset.measurable_prod _ fun τ _ =>
    (meas_dpow bb).comp (meas_Yb.comp (cont_Mx X x0 τ).measurable)

theorem cont_lact (X : Data E r) (γ : GL (Fin r) E) : Continuous (lact (Ψ := X.Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : Frame X.Ψ r =>
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  exact continuous_const.matrix_mul (cont_mat X τ)

theorem meas_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a, ⋂ c, {b : Frame X.Ψ r | c < a → b τ a c = 0}) := by
    ext b
    simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
  · exact (isOpen_ne_fun (cont_mat X τ).matrix_det continuous_const).measurableSet
  · by_cases hca : c < a
    · simp only [hca, true_implies]
      exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
    · simp [hca]

def Sset (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun pr : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 pr.1) pr.2) '' (FF ×ˢ Bor X.Ψ r)

theorem meas_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) : MeasurableSet (Sset X x0 FF) := by
  have : PolishSpace (V (nd X) × Frame X.Ψ r) := {}
  refine MeasurableSet.image_of_continuousOn_injOn (hFF.prod (meas_Bor X)) ?_ ?_
  · refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact ((cont_mat X τ).comp ((cont_cpt X x0).comp continuous_fst)).matrix_mul
      ((cont_mat X τ).comp continuous_snd)
  · rintro ⟨z, b⟩ ⟨_, hb⟩ ⟨z', b'⟩ ⟨_, hb'⟩ h
    obtain ⟨e1, e2⟩ := cpt_inj X ho hb hb' h
    exact Prod.ext e1 e2

private lemma rmul_rmul_eq_rmul_rmul (X : Data E r) (x b c : Frame X.Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)

private lemma bor_rmul_mem (X : Data E r) {b c : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hc : c ∈ Bor X.Ψ r) : rmul b c ∈ Bor X.Ψ r := by
  intro τ
  have hm : mat (rmul b c) τ = mat b τ * mat c τ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
    have h2 : (mat c τ).BlockTriangular id := fun i j h => (hc τ).2 i j h
    exact (h1.mul h2) hda

private lemma inv_mat_mem_bor (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  have hm : mat (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  letI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
  have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular h1) hda

private lemma rmul_rmul_inv_mat (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (y : Frame X.Ψ r) :
    rmul (rmul y b) (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rfl

theorem rmul_mem_S (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ Sset X x0 FF ↔ y ∈ Sset X x0 FF := by
  constructor
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)⟩, ⟨hz, bor_rmul_mem X hc (inv_mat_mem_bor X hb)⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans
      ((congrArg (fun w => rmul w _) h).trans (rmul_rmul_inv_mat X hb y))
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c b⟩, ⟨hz, bor_rmul_mem X hc hb⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans (congrArg (fun w => rmul w b) h)

theorem cpt_mem_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))} (z : V (nd X)) :
    cpt X x0 z ∈ Sset X x0 FF ↔ z ∈ FF := by
  constructor
  · rintro ⟨⟨z', b'⟩, ⟨hz', hb'⟩, h⟩
    simp only at h
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rwa [← (cpt_inj X ho hb' (ExtFPf.oneF_mem X) h).1]
  · intro hz
    exact ⟨⟨z, ExtFPf.oneF X⟩, ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

theorem lact_rmul' (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (rmul x b) τ = mat (lact γ x) τ * mat b τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

theorem lminor_one (k : Fin (r + 1)) : lminor (1 : Matrix (Fin r) (Fin r) ℂ) k = 1 := by
  unfold lminor
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]

theorem orthogonalFrame_delta_eq_one (hx0 : IsOrth X x0) : DeltaF X x0 x0 = 1 := by
  unfold DeltaF
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
  have h : Mx X x0 x0 τ = 1 := by
    unfold Mx
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (orthogonalFrame_det_ne_zero (X := X) (x0 := x0) hx0 τ))
  rw [h, lminor_one]

def linePoly (x v : Frame X.Ψ r) : ℂ[X] :=
  ∏ τ, ∏ k : Fin (r + 1),
    (((Mx X x0 x τ).map C + (Polynomial.X : ℂ[X]) • ((mat x0 τ)⁻¹ * mat v τ).map C).submatrix
      (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det

theorem linePoly_eval (x v : Frame X.Ψ r) (t : ℂ) :
    (linePoly (x0 := x0) x v).eval t = DeltaF X x0 (x + t • v) := by
  unfold linePoly DeltaF lminor
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Mx, mat, Matrix.mul_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_left_comm,
    Polynomial.eval_finsetSum]

theorem dense_delta (hx0 : IsOrth X x0) (x : Frame X.Ψ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ ball x ε, DeltaF X x0 y ≠ 0 := by
  classical
  set w : Frame X.Ψ r := x0 - x
  set P := linePoly (x0 := x0) x w
  have hP1 : P.eval 1 = 1 := by
    rw [linePoly_eval, one_smul, add_sub_cancel, orthogonalFrame_delta_eq_one hx0]
  have hP0 : P ≠ 0 := by
    rintro h
    rw [h, Polynomial.eval_zero] at hP1
    exact zero_ne_one hP1
  set δ : ℝ := ε / (‖w‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hinf : ((fun s : ℝ => (s : ℂ)) '' Set.Ioo 0 δ).Infinite :=
    (Set.Ioo_infinite hδ).image (fun a _ b _ h => Complex.ofReal_injective h)
  obtain ⟨c, hc, hcP⟩ := (hinf.diff (Polynomial.finite_setOf_isRoot hP0)).nonempty
  obtain ⟨s, hs, rfl⟩ := hc
  refine ⟨x + (s : ℂ) • w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖w‖ ≤ δ * ‖w‖ := by gcongr; exact hs.2.le
      _ < δ * (‖w‖ + 1) := by gcongr; linarith
      _ = ε := by
        have : (‖w‖ + 1) ≠ 0 := by positivity
        simp only [δ]
        field_simp
  · rw [← linePoly_eval]
    exact hcP

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lu_holds : LUStatement (E := E) := by
  intro r X x0 hx0
  refine ⟨DeltaF X x0, zF X x0, bF X x0, Delta_diff (X := X) (x0 := x0),
    fun x _ ε hε => dense_delta (X := X) (x0 := x0) hx0 x ε hε,
    zF_diffOn (X := X) (x0 := x0), bF_diffOn (X := X) (x0 := x0),
    fun x hx hΔ => ⟨zF_mem (X := X) (x0 := x0) hx0 hx hΔ, bF_mem (X := X) (x0 := x0) hx hΔ,
      split_eq (X := X) (x0 := x0) hx0 x⟩,
    fun z _ b hb => uniq_all (X := X) (x0 := x0) hx0 hb⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

