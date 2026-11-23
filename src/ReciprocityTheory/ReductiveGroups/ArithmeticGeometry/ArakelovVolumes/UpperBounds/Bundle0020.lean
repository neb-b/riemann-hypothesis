module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Lemmata.GeneralBFactVersion.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0017

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfL
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eLE : LoI X.Ψ r ≃ Ent X where
  toFun i := ⟨i.1.1, ⟨(i.1.2.1, i.1.2.2), i.2⟩⟩
  invFun e := ⟨(e.1, e.2.1.1, e.2.1.2), e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def eL : LoI X.Ψ r ≃ Fin (nd X) := (eLE X).trans (Fintype.equivFin (Ent X))

def ΦL : V (nd X) ≃ₗ[ℂ] (LoI X.Ψ r → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans (LinearEquiv.funCongrLeft ℂ ℂ (eL X))

lemma NF_ΦL (z : V (nd X)) : NF X (ΦL X z) = nmat X z := by
  funext τ a b
  simp only [NF, Nmat, nmat, Matrix.of_apply]
  split_ifs <;> rfl

def muX (x0 : Frame X.Ψ r) : Measure (V (nd X)) :=
  (volume.restrict {z | cpt X x0 z ∈ X.dom}).withDensity fun z => ENNReal.ofReal (densY X (cpt X x0 z))

def ΦC : V (nd X) ≃L[ℂ] (LoI X.Ψ r → ℂ) := (ΦL X).toContinuousLinearEquiv

lemma lintegral_ΦC (F : (LoI X.Ψ r → ℂ) → ENNReal) :
    ∫⁻ z, F (ΦC X z) = Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, F x := by
  have h1 : (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) :=
    (lintegral_map_equiv F (ΦC X).toHomeomorph.toMeasurableEquiv).symm
  calc (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) := h1
    _ = ∫⁻ x, F x ∂(Measure.addHaarScalarFactor (volume.map (ΦC X)) volume • volume) := by
        rw [← Measure.isAddLeftInvariant_eq_smul]
    _ = _ := lintegral_smul_measure _ _

lemma continuous_dmin (τ : X.Ψ) (i : Fin (r + 1)) : Continuous fun y : Frame X.Ψ r => dmin X.Gm y τ i := by
  unfold dmin lminor
  apply Continuous.matrix_det
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC,
    ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat]
  fun_prop

lemma measurable_densY : Measurable (densY X) := by
  have h : densY X = fun y => (∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2)⁻¹ :=
    funext fun y => densY_eq X
  rw [h]
  refine Measurable.inv ?_
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  exact ((continuous_dmin X τ _).measurable.norm).pow_const 2

lemma continuous_NF : Continuous (NF X) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : b < a
  · have e : (fun x : LoI X.Ψ r → ℂ => NF X x τ a b) = fun x => x ⟨(τ, a, b), h⟩ := by
      funext x
      simp [NF, Nmat, h]
    rw [e]
    exact continuous_apply _
  · have e : (fun x : LoI X.Ψ r → ℂ => NF X x τ a b) = fun _ => if a = b then 1 else 0 := by
      funext x
      simp [NF, Nmat, h]
    rw [e]
    exact continuous_const

lemma cpt_eq (x0 : Frame X.Ψ r) (z : V (nd X)) : cpt X x0 z = rmul x0 (NF X (ΦC X z)) := by
  show rmul x0 (nmat X z) = rmul x0 (NF X (ΦC X z))
  rw [← NF_ΦL]
  rfl

lemma continuous_cpt (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  rw [show cpt X x0 = fun z => rmul x0 (NF X (ΦC X z)) from funext (cpt_eq X x0)]
  refine continuous_pi fun τ => ?_
  show Continuous fun z => mat x0 τ * mat (NF X (ΦC X z)) τ
  exact continuous_const.matrix_mul (((continuous_apply τ).comp (continuous_NF X)).comp (ΦC X).continuous)

theorem lintegral_muX {x0 : Frame X.Ψ r} {φ : Frame X.Ψ r → ENNReal} (hφm : Measurable φ) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 =
      Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, GLo X x0 φ x := by
  have hdom : MeasurableSet X.dom := by
    have ho : IsOpen X.dom := by
      show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
      simp only [Set.setOf_forall, Set.setOf_and]
      refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
      · exact isOpen_ne_fun (continuous_apply τ).matrix_det continuous_const
      · exact isOpen_lt continuous_const
          (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin X τ i)))
    exact ho.measurableSet
  have hS : MeasurableSet {z : V (nd X) | cpt X x0 z ∈ X.dom} :=
    hdom.preimage (continuous_cpt X x0).measurable
  have hdens : Measurable fun z => ENNReal.ofReal (densY X (cpt X x0 z)) :=
    ENNReal.measurable_ofReal.comp ((measurable_densY X).comp (continuous_cpt X x0).measurable)
  unfold muX
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens
      (show Measurable fun z => φ (cpt X x0 z) from hφm.comp (continuous_cpt X x0).measurable),
    ← lintegral_indicator hS, ← lintegral_ΦC]
  congr 1
  funext z
  simp [GLo, Set.indicator, cpt_eq, mul_comm]

theorem lintegral_cpt_muX_indep_of_isOrtho {x0 x0' : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (hx0' : X.IsOrtho x0') {φ : Frame X.Ψ r → ENNReal}
    (hφm : Measurable φ) (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muX X x0' := by
  rw [lintegral_muX X hφm, lintegral_muX X hφm]
  congr 1
  have h1 := core X hx0 hφm hφ
  have h2 := core X hx0' hφm hφ
  have hK0 : K0 X.Ψ r ≠ 0 := (finrank_maxUnramifiedSubfield_padicFinExt_pos (ι := X.Ψ) (r := r)).ne'
  have hK0' : K0 X.Ψ r ≠ ⊤ := (measureConstant_lt_top (ι := X.Ψ) (r := r)).ne
  exact (ENNReal.mul_left_inj hK0 hK0').mp (h1.trans h2.symm)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lactDom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X hγ x).2 hx

theorem rmulDom (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb

theorem isOpenDom (X : Data E r) : IsOpen X.dom := FourierCoefficientDomain.isOpen_dom X

theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul]
  rw [Matrix.mul_assoc]
  rfl

theorem lact_rmul' {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

theorem chi_ne (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  intro h
  have := norm_chi X la hγ
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem poin_mul (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ) (hg : X.IsSec la' g)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  dsimp only
  rw [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  have h1 := chi_ne X la' γ.2
  have h2 := chi_ne X la γ.2
  field_simp

theorem poin_rmul (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    poin X la P (rmul x b) = bchar la b * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  rw [lact_rmul', hP _ (lactDom X γ.2 hx) b hb]
  ring

theorem poin_lact (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {γ' : GL (Fin r) E}
    (hγ' : γ' ∈ X.Γ) (x : Frame X.Ψ r) :
    poin X la P (lact γ' x) = X.χ la γ' * poin X la P x := by
  unfold poin
  set g : X.Γ := ⟨γ', hγ'⟩
  have key : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 (lact γ' x)) =
      X.χ la γ' * ((X.χ la (γ * g).1)⁻¹ * P (lact (γ * g).1 x)) := by
    intro γ
    have hm : ((γ * g : X.Γ) : GL (Fin r) E) = γ.1 * γ' := rfl
    rw [hm, lact_mul', X.χ_mul la γ.1 γ.2 γ' hγ']
    have h1 := chi_ne X la hγ'
    have h2 := chi_ne X la γ.2
    field_simp
  rw [tsum_congr key, tsum_mul_left]
  congr 1
  exact (Equiv.mulRight g).tsum_eq (fun δ : X.Γ => (X.χ la δ.1)⁻¹ * P (lact δ.1 x))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open Metric

theorem fderiv_bound_ball {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
    {R M : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball y (2 * R)))
    (hM : ∀ v ∈ ball y (2 * R), ‖g v‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / R := by
  first | exact Bl.general_b_fact_version.goal1 .. | (apply Bl.general_b_fact_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_version.goal1 <;> assumption)

theorem differentiableOn_tsum_loc {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {U : Set Y}
    (hU : IsOpen U) (f : ι → Y → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ y ∈ U, ∃ ε > 0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ v ∈ ball y ε, ‖f i v‖ ≤ u i) :
    DifferentiableOn ℂ (fun y => ∑' i, f i y) U := by
  intro y0 hy0
  obtain ⟨ε, hε, u, hu, hub⟩ := hb y0 hy0
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU y0 hy0
  set m := min ε δ with hm
  have hm0 : 0 < m := lt_min hε hδ
  set R := m / 4 with hR
  have hR0 : 0 < R := by positivity
  have hsub : ∀ y ∈ ball y0 R, ball y (2 * R) ⊆ ball y0 m := by
    intro y hy v hv
    rw [mem_ball] at *
    calc dist v y0 ≤ dist v y + dist y y0 := dist_triangle _ _ _
      _ < 2 * R + R := add_lt_add hv hy
      _ ≤ m := by rw [hR]; linarith
  have hε' : ball y0 m ⊆ ball y0 ε := ball_subset_ball (min_le_left _ _)
  have hδ' : ball y0 m ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hin : ∀ y ∈ ball y0 R, y ∈ U := fun y hy => hδ' (hsub y hy (mem_ball_self (by linarith)))
  have hder : ∀ i, ∀ y ∈ ball y0 R, HasFDerivAt (f i) (fderiv ℂ (f i) y) y := fun i y hy =>
    ((hf i y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))).hasFDerivAt
  have hbd : ∀ i, ∀ y ∈ ball y0 R, ‖fderiv ℂ (f i) y‖ ≤ u i / R := fun i y hy =>
    fderiv_bound_ball hR0 ((hf i).mono ((hsub y hy).trans hδ')) (fun v hv => hub i v (hε' (hsub y hy hv)))
  have hs := hasFDerivAt_tsum_of_isPreconnected (hu.div_const R) isOpen_ball
    (convex_ball y0 R).isPreconnected hder hbd (mem_ball_self hR0)
    (Summable.of_norm_bounded hu fun i => hub i y0 (mem_ball_self hε)) (mem_ball_self hR0)
  exact hs.differentiableAt.differentiableWithinAt

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set Matrix NumberField ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm

def Zmap (z : V (nd X)) : V (nD X.Ψ.card X.p0 (r - X.p0)) :=
  WithLp.toLp 2 fun j => ExF.Zt X z (eΨ X (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2

theorem Zof_Zmap (z : V (nd X)) (k : Fin X.Ψ.card) : Zof (Zmap X z) k = ExF.Zt X z (eΨ X k) := by
  ext a b
  change ExF.Zt X z (eΨ X (finProdFinEquiv.symm (finProdFinEquiv (k, finProdFinEquiv (a, b)))).1) _ _ = _
  simp only [Equiv.symm_apply_apply]

private theorem contDiff_nM_apply (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => ExF.nM X z τ a b := by
  unfold ExF.nM
  simp only [mat, Matrix.of_apply, nmat]
  split_ifs
  · first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  · exact contDiff_const
  · exact contDiff_const

private theorem det_n1_eq_one (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
    simp [nmat]
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    rw [Fin.lt_def] at hlt
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_def]; simp only [Fin.coe_castLE]; omega
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.coe_castLE] at h; omega
    simp only [nmat, dif_neg h1, if_neg h2]

private theorem inv_n1_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ)⁻¹ = (ExF.n1 X z τ).adjugate := by
  rw [Matrix.inv_def, det_n1_eq_one, Ring.inverse_one, one_smul]

private theorem contDiff_det_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) : ContDiff ℂ ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  first
  | exact contDiff_prod fun i _ => hM _ _
  | fun_prop

private theorem contDiff_adjugate_apply_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) (a b : Fin n) :
    ContDiff ℂ ∞ fun z => (M z).adjugate a b := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det_of_contDiff_entries
  intro i j
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hM i j

theorem Zmap_contDiff : ContDiff ℂ ∞ (Zmap X) := by
  have hn1 : ∀ τ : X.Ψ, ∀ i j, ContDiff ℂ ∞ fun z : V (nd X) => ExF.n1 X z τ i j :=
    fun τ i j => contDiff_nM_apply X τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
  have hW : ∀ τ : X.Ψ, ∀ b c, ContDiff ℂ ∞ fun z : V (nd X) => ExF.Wm X z τ b c :=
    fun τ b c => contDiff_nM_apply X τ (ExF.qI X b) (Fin.castLE X.p0_le c)
  refine (contDiff_piLp _).mpr fun j => ?_
  change ContDiff ℂ ∞ fun z : V (nd X) => ExF.Zt X z _ _ _
  simp only [ExF.Zt, Matrix.transpose_apply, inv_n1_eq_adjugate, Matrix.mul_apply]
  exact ContDiff.sum fun c _ => (hW _ _ _).mul (contDiff_adjugate_apply_of_contDiff_entries X (fun z => ExF.n1 X z _) (hn1 _) _ _)

theorem rh_Zmap (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    rh (Zmap X z) = rhF X x0 z := by
  rw [ExF.rhF_eq_sum X x0 ho, rh]
  congr 1
  rw [← (eΨ X).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Zof_Zmap]
  have hpd := (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)
  rw [show (1 - ExF.Zt X z (eΨ X k) * (ExF.Zt X z (eΨ X k))ᴴ) = ExF.Am X z (eΨ X k) from rfl,
    ExF.norm_of_pos hpd.det_pos]

theorem Zmap_mem (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Zmap X z ∈ Dset X.Ψ.card X.p0 (r - X.p0) := by
  intro k
  rw [Zof_Zmap]
  exact (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)

theorem rh_contDiffAt {f p q : ℕ} {v : V (nD f p q)} (hv : v ∈ Dset f p q) :
    ContDiffAt ℝ 2 (fun w : V (nD f p q) => ((rh w : ℝ) : ℂ)) v := by
  have hZ : ∀ k a b, ContDiff ℝ 2 fun w : V (nD f p q) => Zof w k a b := by
    intro k a b
    simp only [Zof, Matrix.of_apply]
    first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  have hM : ∀ k i j, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ : Matrix (Fin p) (Fin p) ℂ) i j := by
    intro k i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine contDiff_const.sub (ContDiff.sum fun l _ => (hZ k i l).mul ?_)
    have h := hZ k j l
    first
    | exact h.star
    | exact Complex.conjCLE.contDiff.comp h
    | fun_prop
  have hdet : ∀ k, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ).det := by
    intro k
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    first
    | exact contDiff_prod fun i _ => hM k _ _
    | fun_prop
  have hpos : ∀ k, 0 < ((1 - Zof v k * (Zof v k)ᴴ).det).re := by
    intro k
    have h := (hv k).det_pos
    first
    | exact (Complex.pos_iff.mp h).1
    | simpa using (Complex.lt_def.mp h).1
  have hlog : ∀ k, ContDiffAt ℝ 2
      (fun w : V (nD f p q) => Real.log ((1 - Zof w k * (Zof w k)ᴴ).det.re)) v := by
    intro k
    have hre : ContDiff ℝ 2 fun w : V (nD f p q) => ((1 - Zof w k * (Zof w k)ᴴ).det).re :=
      Complex.reCLM.contDiff.comp (hdet k)
    exact (Real.contDiffAt_log.mpr (hpos k).ne').comp v hre.contDiffAt
  have hsum : ContDiffAt ℝ 2 (fun w : V (nD f p q) => rh w) v := by
    unfold rh
    exact (ContDiffAt.sum fun k _ => hlog k).neg
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp v hsum

end

theorem rhGradF_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : RhGradFStatement (E := E) := by
  intro r X x0 ho z hz ξ
  have hU := ExF.isOpen_OmF X x0
  have hZ : ContDiff ℂ ∞ (Zmap X) := Zmap_contDiff X
  have hZd : HasFDerivAt (Zmap X) (fderiv ℂ (Zmap X) z) z :=
    (hZ.differentiable (by simp) z).hasFDerivAt
  have hmem := Zmap_mem X x0 ho hz
  have hg := rh_contDiffAt hmem
  have hev : (fun w : V (nd X) => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      (fun w : V (nD X.Ψ.card X.p0 (r - X.p0)) => ((rh w : ℝ) : ℂ)) ∘ Zmap X := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simp only [Function.comp_apply, rh_Zmap X x0 ho hw]
  have h1 : ∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j =
      ∑ a, wd _ a (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) *
        fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) a := by
    rw [← gc_sum_wd_comp _ _ _ _ _ z (hg.differentiableAt (by norm_num)) hZd ξ]
    exact Finset.sum_congr rfl fun j _ => by rw [wd_congr (j := j) (h := hev)]
  have h2 : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ =
      leviV _ (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) (fun b => fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) b) := by
    rw [Y.fc_leviV_congr (nd X) _ _ z hev]
    exact gc_leviV_comp _ _ _ _ Set.univ isOpen_univ z trivial (hZ.contDiffOn.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)) hg ξ
  rw [h1, h2]
  exact RhGradStatement_holds _ _ _ _ hmem _

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem RhGradFStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    RhGradFStatement (E := E) := RGF.rhGradF_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

