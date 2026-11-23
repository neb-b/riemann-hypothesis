module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStartPf

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace BigC

variable {r : ℕ}

private theorem norm_dmin_succ_div_castSucc_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin r) :
    0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
  have h := (hx τ).2
  have h1 := h i.succ
  have h2 := h i.castSucc
  refine norm_pos_iff.mpr (div_ne_zero ?_ ?_)
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro h0
    rw [h0] at h2
    simp at h2

private theorem nfac_pos_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    0 < X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _

private theorem phla_eq_sum_log_norm_dmin_ratio (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    phla X la x = ∑ τ, ∑ i : Fin r,
      (la τ i : ℝ) * Real.log ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
  unfold phla Data.nfac
  rw [Real.log_prod (fun τ _ =>
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos X hx τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (norm_dmin_succ_div_castSucc_pos X hx τ i)]
  ring

theorem phla_sub (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    phla X (la - la') x = phla X la x - phla X la' x := by
  rw [phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

theorem phla_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (k : ℕ) (la : Wt X.Ψ r) :
    phla X (k • la) x = k * phla X la x := by
  rw [phla_eq_sum_log_norm_dmin_ratio X hx, phla_eq_sum_log_norm_dmin_ratio X hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, nsmul_eq_mul]
  push_cast
  ring

theorem log_pnorm_sq (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hP : P x ≠ 0) :
    Real.log (X.pnorm la P x ^ 2) = Real.log (Complex.normSq (P x)) - phla X la x := by
  have hN := nfac_pos_of_mem_dom X hx la
  have hp : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  have hn2 : Complex.normSq (P x) = ‖P x‖ ^ 2 := by
    first
      | exact Complex.normSq_eq_norm_sq _
      | exact (Complex.sq_norm _).symm
      | simp [Complex.normSq_eq_abs]
  rw [hp, mul_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hP)) (pow_ne_zero _ hN.ne'), hn2,
    Real.log_pow, Real.log_pow, phla]
  ring

end BigC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI

noncomputable section

attribute [local instance] Classical.propDecidable

theorem cont_inv {α : Type*} [TopologicalSpace α] {n : ℕ} {f : α → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hd : ∀ a, (f a).det ≠ 0) : Continuous fun a => (f a)⁻¹ := by
  have h : (fun a => (f a)⁻¹) = fun a => (f a).det⁻¹ • (f a).adjugate := by
    funext a
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate

theorem cont_uMat {α : Type*} [TopologicalSpace α] {n : ℕ} {g : α → Matrix (Fin n) (Fin n) ℂ}
    (hg : Continuous g) (hd : ∀ a c, (blk (g a) c).det ≠ 0) : Continuous fun a => uMat (g a) := by
  refine continuous_pi fun j => continuous_pi fun c => ?_
  simp only [uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact continuous_const
  · have hb : Continuous fun a => blk (g a) c := by
      unfold blk
      exact hg.matrix_submatrix _ _
    have hi := cont_inv hb (fun a => hd a c)
    have hr : Continuous fun a => rowc (g a) c := by
      unfold rowc
      exact continuous_pi fun m => (continuous_apply _).comp ((continuous_apply c).comp hg)
    exact ((continuous_apply (⟨j, h2⟩ : Fin c)).comp (hr.matrix_vecMul hi)).neg
  · exact continuous_const

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_mat (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => mat y τ := by
  exact continuous_pi fun a => continuous_pi fun b => continuous_coord X τ a b

private theorem continuous_gram_comp {α : Type*} [TopologicalSpace α] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {f : α → Matrix (Fin r) (Fin r) ℂ} (hf : Continuous f) :
    Continuous fun a => ReciprocityTheory.ChartRestriction.G.FD.gram τ G (f a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply i).comp ((continuous_apply a).comp hf)).mul continuous_const).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply b).comp hf)))

theorem cont_gram (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => gram τ.1 X.Gm (mat y τ) := by
  exact continuous_gram_comp τ.1 X.Gm (cont_mat X τ)

theorem cont_uOf (τ : X.Ψ) : Continuous fun y : X.dom => uOf X y.1 τ := by
  have hg : Continuous fun y : X.dom => gram τ.1 X.Gm (mat y.1 τ) := (cont_gram X τ).comp continuous_subtype_val
  exact cont_uMat hg fun y c => blk_det X y.2 τ c

theorem cont_dOf (τ : X.Ψ) (k : Fin r) : Continuous fun y : X.dom => dOf X y.1 τ k := by
  have hm : Continuous fun y : X.dom => mat y.1 τ * uOf X y.1 τ :=
    ((cont_mat X τ).comp continuous_subtype_val).matrix_mul (cont_uOf X τ)
  exact (continuous_apply k).comp ((continuous_apply k).comp (continuous_gram_comp τ.1 X.Gm hm))

theorem cont_sOf (τ : X.Ψ) (k : Fin r) : Continuous fun y : X.dom => sOf X y.1 τ k := by
  have hd := cont_dOf X τ k
  have hr : Continuous fun y : X.dom => Real.sqrt |(dOf X y.1 τ k).re| :=
    (Complex.continuous_re.comp hd).abs.sqrt
  have hne : ∀ y : X.dom, Real.sqrt |(dOf X y.1 τ k).re| ≠ 0 := fun y =>
    (Real.sqrt_pos.mpr (abs_re_pos X y.2 τ k)).ne'
  exact Complex.continuous_ofReal.comp (hr.inv₀ hne)

theorem cont_bOf (τ : X.Ψ) : Continuous fun y : X.dom => mat (bOf X y.1) τ := by
  exact (cont_uOf X τ).matrix_mul (Continuous.matrix_diagonal (continuous_pi fun k => cont_sOf X τ k))

theorem cont_β0 (τ : X.Ψ) : Continuous fun y : X.dom => β0 X y.1 τ := by
  exact cont_inv (cont_bOf X τ) (fun y => bOf_det X y.2 τ)

theorem β0_bound {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∃ R0 : ℝ, ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0 := by
  have hcont : ∀ (τ : X.Ψ) (a b : Fin r), ContinuousOn (fun x => ‖β0 X x τ a b‖) C := by
    intro τ a b
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun y : X.dom => ‖β0 X y.1 τ a b‖ :=
      ((continuous_apply b).comp ((continuous_apply a).comp (cont_β0 X τ))).norm
    show Continuous fun x : C => ‖β0 X x.1 τ a b‖
    refine (h1.comp (continuous_inclusion hCd)).congr fun x => ?_
    simp only [Function.comp_apply, Set.coe_inclusion]
  choose R hR using fun (τ : X.Ψ) (a b : Fin r) => hC.bddAbove_image (hcont τ a b)
  refine ⟨∑ τ, ∑ a, ∑ b, max (R τ a b) 0, fun x hx τ a b => ?_⟩
  have h1 : ‖β0 X x τ a b‖ ≤ R τ a b := hR τ a b ⟨x, hx, rfl⟩
  calc ‖β0 X x τ a b‖ ≤ max (R τ a b) 0 := h1.trans (le_max_left _ _)
    _ ≤ ∑ b', max (R τ a b') 0 :=
        Finset.single_le_sum (f := fun b' => max (R τ a b') 0) (fun _ _ => le_max_right _ _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', max (R τ a' b') 0 :=
        Finset.single_le_sum (f := fun a' => ∑ b', max (R τ a' b') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ a)
    _ ≤ ∑ τ', ∑ a', ∑ b', max (R τ' a' b') 0 :=
        Finset.single_le_sum (f := fun τ' => ∑ a', ∑ b', max (R τ' a' b') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _)
          (Finset.mem_univ τ)

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FSM

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private theorem rmul_rmul' {Ψ : Finset (E →+* ℂ)} (x a b : Frame Ψ r) :
    rmul (rmul x a) b = rmul x (rmul a b) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)

private theorem rmul_mem_bor_upper_bounds {Ψ : Finset (E →+* ℂ)} {a b : Frame Ψ r} (ha : a ∈ Bor Ψ r)
    (hb : b ∈ Bor Ψ r) : rmul a b ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1

private theorem mem_bor_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : c ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => ?_⟩
  · rw [hc τ]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero
  · have h2 := hI h
    rw [← hc τ] at h2
    exact h2

private theorem rmul_rmul_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : rmul (rmul x b) c = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * mat c τ = x τ
  rw [hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl

private theorem lact_rmul_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

private theorem lact_lact' {Ψ : Finset (E →+* ℂ)} (γ δ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private theorem lact_inv_lact_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact', inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl

theorem atMostOnce (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) (y : Frame X.Ψ r) :
    ∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) ≤ 1 := by
  unfold IsFundSet at hFF
  obtain ⟨_, hFO, hFinj, _⟩ := hFF
  have hS : ∀ w, w ∈ KU.Sset X x0 FF → ∃ z ∈ FF, ∃ b ∈ Bor X.Ψ r, w = rmul (cpt X x0 z) b := by
    intro w hw
    simp only [KU.Sset] at hw
    obtain ⟨⟨z, b⟩, ⟨hz, hb⟩, he⟩ := hw
    exact ⟨z, hz, b, hb, he.symm⟩
  have huniq : ∀ γ γ0 : X.Γ, lact γ.1 y ∈ KU.Sset X x0 FF → lact γ0.1 y ∈ KU.Sset X x0 FF →
      γ = γ0 := by
    intro γ γ0 h1 h2
    obtain ⟨z, hz, b, hb, hzb⟩ := hS _ h1
    obtain ⟨z0, hz0, b0, hb0, hzb0⟩ := hS _ h2
    have hg : γ.1 * γ0.1⁻¹ ∈ X.Γ := X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2)
    have hy : y = lact γ0.1⁻¹ (rmul (cpt X x0 z0) b0) := by
      rw [← hzb0, lact_inv_lact_upper_bounds]
    have hst : rmul (lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0)) b0 = rmul (cpt X x0 z) b := by
      rw [← lact_rmul_upper_bounds, ← lact_lact', ← hy, hzb]
    obtain ⟨bi, hbi⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b τ)⁻¹ :=
      ⟨(fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    obtain ⟨bi0, hbi0⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b0 τ)⁻¹ :=
      ⟨(fun τ => ((mat b0 τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    have hw : cpt X x0 z = lact (γ.1 * γ0.1⁻¹) (rmul (cpt X x0 z0) (rmul b0 bi)) := by
      rw [lact_rmul_upper_bounds, ← rmul_rmul', hst, rmul_rmul_of_mat_eq_inv _ hb hbi]
    have hzz : z0 = z := hFinj z0 hz0 z hz _ hg _ (rmul_mem_bor_upper_bounds hb0 (mem_bor_of_mat_eq_inv hb hbi)) hw
    subst hzz
    have hw0 : cpt X x0 z0 ∈ X.dom := hFO hz0
    have hfix : lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0) = rmul (cpt X x0 z0) (rmul b bi0) := by
      rw [← rmul_rmul', ← hst, rmul_rmul_of_mat_eq_inv _ hb0 hbi0]
    have hg1 : γ.1 * γ0.1⁻¹ = 1 := X.Γ_free _ hg _ hw0 _ (rmul_mem_bor_upper_bounds hb (mem_bor_of_mat_eq_inv hb0 hbi0)) hfix
    exact Subtype.ext (mul_inv_eq_one.mp hg1)
  by_cases hex : ∃ γ0 : X.Γ, lact γ0.1 y ∈ KU.Sset X x0 FF
  · obtain ⟨γ0, hγ0⟩ := hex
    rw [tsum_eq_single γ0]
    · rw [Set.indicator_of_mem hγ0]
      simp
    · intro γ hne
      exact Set.indicator_apply_eq_zero.mpr fun hm => absurd (huniq γ γ0 hm hγ0) hne
  · push_neg at hex
    have h0 : ∀ γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) = 0 :=
      fun γ => Set.indicator_apply_eq_zero.mpr fun hm => absurd hm (hex γ)
    rw [tsum_congr h0, tsum_zero]
    exact zero_le_one

end

theorem fundSetMeasStatement_of_isCMField {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FundSetMeasStatement (E := E) := by
  intro r X x0 FF ho hFF ⟨x1, ho1, CechHodgeFiltration, hFF1, hfin⟩
  classical
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  have hS : MeasurableSet (KU.Sset X x0 FF) := KU.meas_S X ho hFF.1
  have hS1 : MeasurableSet (KU.Sset X x1 CechHodgeFiltration) := KU.meas_S X ho1 hFF1.1
  have hcpt0 := (KU.cont_cpt X x0).measurable
  have hcpt1 := (KU.cont_cpt X x1).measurable

  set Bad : Set (Frame X.Ψ r) := ⋂ γ : X.Γ, (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration)ᶜ with hBaddef
  have hBad : MeasurableSet Bad :=
    MeasurableSet.iInter fun γ => ((KU.cont_lact X γ.1⁻¹).measurable hS1).compl
  have hBadB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Bad.indicator 1 x := by
    intro x _ b hb
    have e : rmul x b ∈ Bad ↔ x ∈ Bad := by
      simp only [hBaddef, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage, KU.lact_rmul',
        KU.rmul_mem_S X hb]
    by_cases h : x ∈ Bad
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (e.mpr h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (e.mp h'))]
  have h1 : ∫⁻ z, Bad.indicator 1 (cpt X x1 z) ∂muF X x1 = 0 := by
    have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x1 z) :=
      (measurable_one.indicator hBad).comp hcpt1
    rw [lintegral_eq_zero_iff hm]
    filter_upwards [KU.cover X hFF1] with z ⟨γ, hγ, hSz⟩
    have : cpt X x1 z ∉ Bad := fun h => (Set.mem_iInter.mp h ⟨γ, hγ⟩) hSz
    simp [Set.indicator_of_notMem this]
  have h0 : ∫⁻ z, Bad.indicator 1 (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ (measurable_one.indicator hBad) hBadB]; exact h1
  have hcov : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad := by
    have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) :=
      (measurable_one.indicator hBad).comp hcpt0
    have := (lintegral_eq_zero_iff hm).mp h0
    filter_upwards [this] with z hz hb
    simp [Set.indicator_of_mem hb] at hz

  let H : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ y =>
    (KU.Sset X x0 FF).indicator 1 y * (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration).indicator 1 y
  have hHm : ∀ γ, Measurable (H γ) := fun γ =>
    (measurable_one.indicator hS).mul (measurable_one.indicator ((KU.cont_lact X γ.1⁻¹).measurable hS1))
  have hHB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, H γ (rmul x b) = H γ x := by
    intro γ x _ b hb
    have e1 : rmul x b ∈ KU.Sset X x0 FF ↔ x ∈ KU.Sset X x0 FF := KU.rmul_mem_S X hb
    have e2 : rmul x b ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration ↔ x ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration := by
      simp only [Set.mem_preimage, KU.lact_rmul', KU.rmul_mem_S X hb]
    simp only [H, Set.indicator_apply, e1, e2, Pi.one_apply]
  have step1 : muF X x0 FF = ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_indicator_one hFF.1]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ FF
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((KU.cpt_mem_S X ho z).mpr hz)]; rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((KU.cpt_mem_S X ho z).mp h))]
  have step2 : ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_mono_ae (hcov.mono fun z hz => ?_)
    by_cases hS0 : cpt X x0 z ∈ KU.Sset X x0 FF
    · have : ∃ γ : X.Γ, cpt X x0 z ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration := by
        by_contra hn
        push_neg at hn
        exact hz (Set.mem_iInter.mpr fun γ => hn γ)
      obtain ⟨γ, hγ⟩ := this
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum γ)
      simp only [H, Set.indicator_of_mem hS0, Set.indicator_of_mem hγ, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hS0]; exact bot_le
  have step3 : ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 = ∑' γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((hHm γ).comp hcpt0).aemeasurable
  have hae1 : ∀ᵐ z ∂muF X x1, z ∈ OmF X x1 := ExtFPf.ae_OmF (X := X) (x0 := x1)
  have step4 : ∀ γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
        (lact γ.1 (cpt X x1 z))) z ∂muF X x1 := by
    intro γ
    rw [hM r X x0 (lact γ.1 x1) ho (KU.isOrth_lact X γ.2 ho1) (H γ) (hHm γ) (hHB γ), KU.muF_lact X γ.2]
    refine lintegral_congr fun z => ?_
    rw [KU.cpt_lact]
    simp only [H]
    have e : lact γ.1 (cpt X x1 z) ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration ↔ z ∈ CechHodgeFiltration := by
      rw [Set.mem_preimage, KU.lact_lact, inv_mul_cancel, KU.lact_one, KU.cpt_mem_S X ho1]
    by_cases hz : z ∈ CechHodgeFiltration
    · rw [Set.indicator_of_mem (e.mpr hz), Set.indicator_of_mem hz, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hz (e.mp h)), Set.indicator_of_notMem hz, mul_zero]
  have hI : ∀ γ : X.Γ, Measurable fun z => CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator
      (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 (cpt X x1 z))) z := fun γ =>
    ((measurable_one.indicator hS).comp ((KU.cont_lact X γ.1).comp (KU.cont_cpt X x1)).measurable).indicator hFF1.1
  have step5 : ∑' γ : X.Γ, ∫⁻ z, CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (lact γ.1 (cpt X x1 z))) z ∂muF X x1 ≤ muF X x1 CechHodgeFiltration := by
    rw [← lintegral_tsum fun γ => (hI γ).aemeasurable, ← lintegral_indicator_one hFF1.1]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ CechHodgeFiltration
    · simp only [Set.indicator_of_mem hz, Pi.one_apply]
      exact FSM.atMostOnce X ho hFF _
    · simp [Set.indicator_of_notMem hz]
  calc muF X x0 FF = _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ = _ := tsum_congr step4
    _ ≤ muF X x1 CechHodgeFiltration := step5
    _ < ⊤ := hfin

end ReciprocityTheory.ChartRestriction.G.AR.Up.FSM

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem FundSetMeasStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FundSetMeasStatement (E := E) := FSM.fundSetMeasStatement_of_isCMField

theorem DivStartStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DivStartStatement (E := E) := DivSt.divStart_of FundSetMeasStatement_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

