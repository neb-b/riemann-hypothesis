module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionOrthonormalHermitianFrames
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem lowerSemicontinuousOn_sum_pos_mul {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (I : Finset ℕ) (e : ℕ → ℝ) (he : ∀ i, 0 < e i) (α : ℕ → Y → ℝ)
    (hα : ∀ i ∈ I, LowerSemicontinuousOn (α i) s) :
    LowerSemicontinuousOn (fun x => ∑ i ∈ I, e i * α i x) s := by
  have key : ∀ i ∈ I, LowerSemicontinuousOn (fun x => e i * α i x) s := by
    intro i hi x hx y hy
    have h1 : y / e i < α i x := by
      rw [div_lt_iff₀ (he i)]
      linarith
    filter_upwards [hα i hi x hx (y / e i) h1] with z hz
    rw [gt_iff_lt, div_lt_iff₀ (he i)] at hz
    show y < e i * α i z
    linarith
  exact lowerSemicontinuousOn_sum key

theorem exists_drift_function_orthFrames : (∀ (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | IsOrth X x} ∧ (∀ x, IsOrth X x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x, IsOrth X x → f (lact γ x) = f x) ∧ (∀ x, IsOrth X x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → f x ≤ M → ε ≤ X.la1 x) := by
  intro r X hp0 hp0r τ0 S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_subspaceHeight_gramDeterminant r X
  obtain ⟨δ, hδ, hdrift⟩ := GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames r X d hd τ0 S hS hirr hU
  obtain ⟨α, hlub, hlsc⟩ := exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hdr⟩ := hdrift α hlub
  have hdet : ∀ x, IsOrth X x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun x hx => (GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx).1
  have hr : 0 < r := lt_trans hp0 hp0r
  have hlow : ∀ x, IsOrth X x → ∀ i ≤ r, ∀ W : Submodule E (Fin r → E),
      Module.finrank E W = i → 0 < d x W ∧ d x W ^ (-δ) ≤ α i x := by
    intro x hx i hi W hW
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x (hdet x hx)
    exact ⟨lt_of_lt_of_le hm (hmW W), (hlub i hi x (hdet x hx)).1 ⟨W, hW, rfl⟩⟩
  have hαnn : ∀ x, IsOrth X x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨hpos, hle⟩ := hlow x hx i hi W hW
    exact le_trans (Real.rpow_nonneg hpos.le _) hle
  have hterm_nn : ∀ x, IsOrth X x → ∀ i ∈ Finset.Ioo 0 r, 0 ≤ e i * α i x := fun x hx i hi =>
    mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hdr, ?_⟩
  · exact lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi =>
      (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hdet x hx
  · intro x hx
    exact Finset.sum_nonneg (hterm_nn x hx)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [GlobalTheory.T.heightSup_invariant_under_hermitianLattice_aut r X d hd δ α hlub γ hγ x (hdet x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨Nat.one_pos, lt_of_le_of_lt hp0 hp0r⟩
    set K : ℝ := max (M / e 1) 1 with hK
    have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨ε, hε, hεla⟩ := GlobalTheory.T.firstMinimum_lower_of_lineHeights r X d hd hr (K ^ (-1 / δ)) (Real.rpow_pos_of_pos hKpos _)
    refine ⟨ε, hε, fun x hx hfM => hεla x hx fun W hW => ?_⟩
    obtain ⟨hpos, hle⟩ := hlow x hx 1 (Finset.mem_Ioo.1 h1).2.le W hW
    have hsingle : e 1 * α 1 x ≤ M :=
      le_trans (Finset.single_le_sum (hterm_nn x hx) h1) hfM
    have hdK : d x W ^ (-δ) ≤ K := by
      refine le_trans hle (le_trans ?_ (le_max_left _ _))
      rw [le_div_iff₀ (he 1)]
      linarith
    have hpow : K ^ (-1 / δ) ≤ (d x W ^ (-δ)) ^ (-1 / δ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hpos _) hdK
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hδ.le)
    rwa [← Real.rpow_mul hpos.le, show -δ * (-1 / δ) = 1 by field_simp, Real.rpow_one] at hpow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.NormFactor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma nfac_eq_prod_norm_dmin_ratio_rpow {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la x = ∏ τ, ∏ i : Fin r,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma blockTriangular_id_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r)
    (τ : Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  intro a c hca
  exact (hb τ).2 a c hca

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mat_diag_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (j : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ j j ≠ 0 := by
  have hdet := (show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0 by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb; exact (hb τ).1)
  rw [Matrix.det_of_upperTriangular (blockTriangular_id_of_mem_bor hb τ)] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet j (Finset.mem_univ j)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    ∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => mat_diag_ne_zero_of_mem_bor hb τ _

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma gram_rmul_eq_transpose_mul_gram {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).transpose * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ) := by
  have hmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
    conv_lhs => unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    rfl
  rw [hmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma dmin_rmul_eq_diag_prod_mul_conj {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i = (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i * starRingEnd ℂ (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [gram_rmul_eq_transpose_mul_gram]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (blockTriangular_id_of_mem_bor hb τ) i

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_succ {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) :
    ∏ j : Fin (i.succ : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) =
      (∏ j : Fin (i.castSucc : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) * M i i := by
  show ∏ j : Fin ((i : ℕ) + 1), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) = _
  rw [Fin.prod_univ_castSucc]
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma norm_ratio_rmul_lemma_2 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.castSucc‖ =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ 2 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
  have hp := diag_prod_ne_zero_of_mem_bor hb τ i.castSucc
  rw [dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.succ, dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.castSucc, diag_prod_succ]
  simp only [norm_div, norm_mul, map_mul, RCLike.norm_conj]
  have hp' : ‖∏ j : Fin (i.castSucc : ℕ), _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)‖ ≠ 0 :=
    norm_ne_zero_iff.2 hp
  by_cases hm : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ = 0
  · simp [hm]
  · field_simp

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rpow_sq_mul_eq_inv_zpow_mul_rpow {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (l : ℤ) :
    (d ^ 2 * t) ^ (-(l : ℝ) / 2) = (d ^ l)⁻¹ * t ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) ht, ← Real.rpow_natCast, ← Real.rpow_mul hd]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg hd,
    Real.rpow_intCast]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.nfac la x := by
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp_rw [norm_ratio_rmul_lemma_2 X x b hb, rpow_sq_mul_eq_inv_zpow_mul_rpow (norm_nonneg _) (norm_nonneg _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hbc : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ = ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp [norm_prod, norm_zpow]
  have hne : ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (mat_diag_ne_zero_of_mem_bor hb τ i))
  rw [hbc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.nfacRmul_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement
  intro r X la x hx b hb
  have hne : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne X la hb)
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  exact _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.dmin_lact {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ x τ]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.nfacLact_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement
  intro r X la γ hγ x _
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp only [_root_.GlobalTheory.NormFactor.dmin_lact X hγ]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.pnormInv_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [nfac_eq_prod_norm_dmin_ratio_rpow]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP
  obtain ⟨-, hPb, hPγ⟩ := hP
  have hxb := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
  have hlact := _root_.GlobalTheory.NormFactor.nfacLact_holds (E := E)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hlact
  rw [hpn, hpn, hPγ γ hγ _ hxb, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hlact r X la γ hγ _ hxb,
    hPb x hx b hb, norm_mul, ← _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb]
  ring


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.NormFactor.nfac_transform :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) :=
  ⟨_root_.GlobalTheory.NormFactor.nfacRmul_holds, _root_.GlobalTheory.NormFactor.nfacLact_holds, _root_.GlobalTheory.NormFactor.pnormInv_holds⟩

end GlobalTheory.NormFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealTsumSqLeTsumDivMulTsum
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ofReal_tsum_sq_le_tsum_div_mul_tsum {ι : Type*} (a k : ι → ℝ) (hs : Summable a)
    (hk : ∀ i, 0 < k i) :
    ENNReal.ofReal ((∑' i, a i) ^ 2) ≤
      (∑' i, ENNReal.ofReal (a i ^ 2 / k i)) * ∑' i, ENNReal.ofReal (k i) := by
  have ht : Filter.Tendsto (fun s : Finset ι => ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal ((∑' i, a i) ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.pow hs.hasSum 2)
  refine le_of_tendsto' ht fun s => ?_
  have h1 : (∑ i ∈ s, a i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i / Real.sqrt (k i))
      (fun i => Real.sqrt (k i))
    have e1 : ∀ i, a i / Real.sqrt (k i) * Real.sqrt (k i) = a i := fun i =>
      div_mul_cancel₀ _ (Real.sqrt_pos.2 (hk i)).ne'
    have e2 : ∀ i, Real.sqrt (k i) ^ 2 = k i := fun i => Real.sq_sqrt (hk i).le
    simp only [e1, div_pow, e2] at h0
    exact h0
  have hd : ∀ i, 0 ≤ a i ^ 2 / k i := fun i => div_nonneg (sq_nonneg _) (hk i).le
  calc ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)
      ≤ ENNReal.ofReal ((∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i) := ENNReal.ofReal_le_ofReal h1
    _ = (∑ i ∈ s, ENNReal.ofReal (a i ^ 2 / k i)) * ∑ i ∈ s, ENNReal.ofReal (k i) := by
      rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => hd i),
        ENNReal.ofReal_sum_of_nonneg fun i _ => hd i,
        ENNReal.ofReal_sum_of_nonneg fun i _ => (hk i).le]
    _ ≤ _ := mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s)

theorem ae_mem_OmF_muF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (OntoB.isOpen_OmF X x0).measurableSet)

theorem poincare_sqIntegrable_fundSet :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) := by
  intro hunf r X x0 hx0 la W bb κ hκ hW _ F P hF hP hPF hsum FF hFF
  obtain ⟨hκm, hκp, hκB, hκa, ⟨C, hC, hκC⟩, -⟩ := hκ
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ with hψ
  have hψm : Measurable ψ :=
    (OntoE.phiF_meas X hP.1.continuousOn hW.1).mul hκm.inv.ennreal_ofReal
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [hψ, OntoE.phiF_B X hP.2 hW x hx b hb, hκB x hx b hb]
  have hψd : ∀ x ∈ X.dom, ψ x = ENNReal.ofReal (‖P x‖ ^ 2 / κ x) * W x := by
    intro x hx
    simp only [hψ, OntoE.phiF_dom X P W hx]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  have hfin : ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hF
    filter_upwards [ae_mem_OmF_muF X x0] with z hz
    rw [hψd _ hz, hPF z hz, hκa z hz]
  rw [hunf r X x0 hx0 FF hFF ψ hψm hψB] at hfin
  have hpt : ∀ x ∈ X.dom, ENNReal.ofReal (‖poin X la P x‖ ^ 2) * W x ≤
      C * ∑' γ : X.Γ, ψ (lact γ.1 x) := by
    intro x hx
    have hγx : ∀ γ : X.Γ, lact γ.1 x ∈ X.dom := fun γ => OntoS.dom_lact X γ.2 hx
    have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := by
      intro γ
      rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have h1 : ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ :=
      norm_tsum_le_tsum_norm (hsum x hx)
    have h2 := ofReal_tsum_sq_le_tsum_div_mul_tsum _ (fun γ : X.Γ => κ (lact γ.1 x)) (hsum x hx)
      fun γ => (hκp _ (hγx γ)).1
    have h3 : ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 x)) ≤ C := by
      refine le_trans (ENNReal.tsum_le_tsum fun γ => ENNReal.ofReal_le_ofReal ?_) (hκC x hx)
      obtain ⟨h0, h1⟩ := hκp _ (hγx γ)
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have h4 : ∑' γ : X.Γ, ψ (lact γ.1 x) =
        (∑' γ : X.Γ, ENNReal.ofReal (‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ ^ 2 / κ (lact γ.1 x))) *
          W x := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [hψd _ (hγx γ), hn, hW.2.2 γ.1 γ.2 x hx]
    rw [h4, ← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    calc ENNReal.ofReal (‖poin X la P x‖ ^ 2)
        ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      _ ≤ _ := h2
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' h3 le_rfl
  unfold InFF
  calc _ ≤ ∫⁻ z in FF, C * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 fun z hz => hpt _ (hFF.2.1 hz)
    _ = C * ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        lintegral_const_mul' _ _ hC.ne
    _ < ⊤ := ENNReal.mul_lt_top hC hfin

end GlobalTheory
end

