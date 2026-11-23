module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.OrthFrameMahler

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuousOn_rmul_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by
  refine continuousOn_pi.2 fun τ => continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => ?_
  show ContinuousOn (fun y : Frame Ψ r => ∑ k, y τ a k * β y τ k c) K
  refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul (by fun_prop) ?_
  exact continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_pi.1 hβ τ) k) c

theorem norm_apply_le_of_diagonal {Ψ : Finset (E →+* ℂ)} {r : ℕ} (z t : Frame Ψ r)
    (hdiag : ∀ τ a, ‖t τ a a‖ = 1 ∧ ∀ c, c ≠ a → t τ a c = 0) (τ : Ψ) (a c : Fin r) :
    ‖z τ a c‖ ≤ ‖rmul z t‖ := by
  have h1 : rmul z t τ a c = z τ a c * t τ c c := by
    show ∑ k, z τ a k * t τ k c = _
    refine Finset.sum_eq_single c (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ c) h)
    rw [(hdiag τ k).2 c (Ne.symm hk), mul_zero]
  calc ‖z τ a c‖ = ‖rmul z t τ a c‖ := by
        rw [h1, norm_mul, (hdiag τ c).1, mul_one]
    _ ≤ ‖rmul z t τ a‖ := norm_le_pi_norm _ c
    _ ≤ ‖rmul z t τ‖ := norm_le_pi_norm _ a
    _ ≤ ‖rmul z t‖ := norm_le_pi_norm _ τ

theorem exists_bound_orthonormal_frame :
    (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x →
      ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  intro r X ε hε
  obtain ⟨K, hKc, hKd, hK⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨β, hβc, hβ⟩ := GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt (E := E) r X
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn (continuousOn_rmul_self (hβc.mono hKd))
  refine ⟨R, fun x hx hla => ?_⟩
  obtain ⟨γ, hγ, b, hb, hy⟩ := hK x (IW.orth_mem_dom X x hx) hla
  refine ⟨γ, X.Γ_stab γ hγ, fun τ a c => ?_⟩
  obtain ⟨hβb, hβo⟩ := hβ _ (hKd hy)
  have hRy : ‖rmul (lact γ (rmul x b)) (β (lact γ (rmul x b)))‖ ≤ R := hR _ hy
  generalize β (lact γ (rmul x b)) = s at hβb hβo hRy
  rw [FundSetPf.lact_rmul, ExtFPf.rmul_assoc] at hβo hRy
  have hγo : IsOrth X (lact γ x) := fun σ => by rw [OntoS.gram_lact X hγ]; exact hx σ
  have hdiag := (GlobalTheory.isOrth_rmul_iff_unitary_diagonal r X _ _ hγo (ExtFPf.mul_mem X hb hβb)).1 hβo
  exact (norm_apply_le_of_diagonal _ _ hdiag τ a c).trans hRy

end GlobalTheory.OrthFrameMahler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroupStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_drift_function_realUnitaryGroup : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  first | exact @GlobalTheory.DriftUnitary.exists_drift_function | exact GlobalTheory.DriftUnitary.exists_drift_function | (intros; apply GlobalTheory.DriftUnitary.exists_drift_function <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GrpSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def dev {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : Frame Ψ r) (γ : GL (Fin r) E) :
    Frame Ψ r :=
  fun τ => ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1 :
    Matrix (Fin r) (Fin r) ℂ)

noncomputable def shift {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 M : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x0 τ * (mat M τ + 1) : Matrix (Fin r) (Fin r) ℂ)

noncomputable def oneF (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

end GlobalTheory.GrpSep

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma sgn_ne_zero_torus_haar_measure (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma det_mat_ne_zero_of_isOrth' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (τ : X.Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (h τ)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at this
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast sgn_ne_zero_torus_haar_measure X.p0 a) this.symm

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_dom_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) : x0 ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  refine fun τ => ⟨det_mat_ne_zero_of_isOrth' X h τ, fun i => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [h τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  rw [← Complex.ofReal_prod, Complex.ofReal_re,
    Fin.prod_univ_eq_prod_range (fun j => _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j) i]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  exact mul_self_pos.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => sgn_ne_zero_torus_haar_measure X.p0 a)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma continuous_shift' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    Continuous (fun M : Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : Ψ → Fin r → Fin r → ℂ)) := by
  unfold _root_.GlobalTheory.GrpSep.shift _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul ((continuous_apply τ).add continuous_const)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_zero_torus_haar_measure {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.GlobalTheory.GrpSep.shift x0 0 = x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * (0 + 1) = x0 τ
  rw [zero_add, Matrix.mul_one]; rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_pos_le_of_finite_pos {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) : ∃ δ > 0, ∀ a ∈ S, δ ≤ f a := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨a0, ha0, hmin⟩ := Set.exists_min_image S f hS h
    exact ⟨f a0, hf a0 ha0, hmin⟩

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma oneF_mem_bor {Ψ : Finset (E →+* ℂ)} {r : ℕ} :
    _root_.GlobalTheory.GrpSep.oneF Ψ r ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
  refine fun τ => ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · change (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne h.ne'

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_dev_eq_lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r)
    (hdet : ∀ τ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0) (γ : GL (Fin r) E) :
    _root_.GlobalTheory.GrpSep.shift x0 (_root_.GlobalTheory.GrpSep.dev x0 γ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1 + 1) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  rw [sub_add_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rmul_oneF' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x0 (_root_.GlobalTheory.GrpSep.oneF Ψ r) = x0 := by
  funext τ
  change (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * 1 : Matrix (Fin r) (Fin r) ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  exact Matrix.mul_one _


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.grpSep : ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r),
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X →
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r),
      c ≤ ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1) a b‖ := by
  intro r X x0 hO hP
  have hdom := mem_dom_of_isOrth X hO
  have hdet := det_mat_ne_zero_of_isOrth' X hO
  obtain ⟨U, hU, U', hU', hfin⟩ := hP x0 hdom x0 hdom
  have hV : (fun M : X.Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : X.Ψ → Fin r → Fin r → ℂ)) ⁻¹' U' ∈
      nhds (0 : X.Ψ → Fin r → Fin r → ℂ) :=
    (continuous_shift' x0).continuousAt.preimage_mem_nhds (by erw [shift_zero_torus_haar_measure]; exact hU')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let S : Set (GL (Fin r) E) :=
    {γ | γ ∈ {γ | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ u = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul u' b} \ ({1} : Set (GL (Fin r) E))}
  obtain ⟨δ, hδ, hmin⟩ := exists_pos_le_of_finite_pos S (hfin.subset (fun _ h => Set.sdiff_subset h))
    (fun γ => ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖) (by
      rintro γ ⟨hγ, h1⟩
      refine norm_pos_iff.mpr fun h0 => h1 (Set.mem_singleton_iff.mpr ?_)
      refine X.Γ_free γ hγ.1 x0 hdom (_root_.GlobalTheory.GrpSep.oneF X.Ψ r) oneF_mem_bor ?_
      rw [← shift_dev_eq_lact x0 hdet, rmul_oneF']
      exact (congrArg (_root_.GlobalTheory.GrpSep.shift x0) h0).trans (shift_zero_torus_haar_measure x0))
  refine ⟨min ε δ, lt_min hε hδ, fun γ hγ h1 => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖ < min ε δ := by
    refine (pi_norm_lt_iff (lt_min hε hδ)).mpr fun τ => (pi_norm_lt_iff (lt_min hε hδ)).mpr
      fun a => (pi_norm_lt_iff (lt_min hε hδ)).mpr fun b => hcon τ a b
  have hmem : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 ∈ U' := by
    rw [← shift_dev_eq_lact x0 hdet]
    exact hball (mem_ball_zero_iff.mpr (hlt.trans_le (min_le_left _ _)))
  have hS := hmin γ ⟨⟨hγ, x0, mem_of_mem_nhds hU, _, hmem, _root_.GlobalTheory.GrpSep.oneF X.Ψ r,
    oneF_mem_bor, (rmul_oneF' _).symm⟩, h1⟩
  exact absurd hS (not_le.mpr (hlt.trans_le (min_le_right _ _)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def uStabSubgroup {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (GL (Fin r) E) where
  carrier := {γ | IsUStab G Λ γ}
  one_mem' := by simp [IsUStab]
  mul_mem' := fun {γ δ} hγ hδ => by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.1, hδ.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hγ.2, ← hδ.2]
  inv_mem' := fun h => isUStab_inv h


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X H _
  refine ⟨((_root_.GlobalTheory.FiniteCovolume.uStabSubgroup X.Gm X.Λ).map (_root_.GlobalTheory.FiniteCovolume.embGL X.Ψ)).comap
    H.subtype, fun g => ?_⟩
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, fun τ => ?_⟩
    rw [← hg, _root_.GlobalTheory.FiniteCovolume.embGL_val]
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, funext fun τ => Units.ext ?_⟩
    rw [_root_.GlobalTheory.FiniteCovolume.embGL_val, hg]

end GlobalTheory.FiniteCovolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

end GlobalTheory.FiniteCovolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOpenSaturation
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (lact δ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem isOpen_cell {r : ℕ} (X : Data E r) {x1 : Frame X.Ψ r} (ho : IsOrth X x1)
    {N : Set (V (nd X))} (hN : IsOpen N) (hNO : N ⊆ OmF X x1) :
    IsOpen {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x1 ho
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have heq : {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} =
      {x | x ∈ X.dom ∧ Δ x ≠ 0} ∩ zOf ⁻¹' N := by
    ext x
    constructor
    · rintro ⟨y, hy, b, hb, rfl⟩
      obtain ⟨h1, h2, -⟩ := huniq y (hNO hy) b hb
      refine ⟨⟨OntoS.dom_rmul X (hNO hy) hb, h1⟩, ?_⟩
      rw [Set.mem_preimage, h2]
      exact hy
    · rintro ⟨⟨hx, hd⟩, hzN⟩
      obtain ⟨-, h2, h3⟩ := hsplit x hx hd
      exact ⟨zOf x, hzN, bOf x, h2, h3⟩
  rw [heq]
  exact hz.continuousOn.isOpen_inter_preimage hU hN

theorem isOpen_saturation : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 →
    ∀ N : Set (V (nd X)), IsOpen N → N ⊆ OmF X x1 →
    IsOpen {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} := by
  intro r X x1 ho N hN hNO
  have heq : {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} =
      ⋃ γ ∈ X.Γ, lact γ⁻¹ ⁻¹' {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨γ, hγ, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
    · rintro ⟨γ, hγ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ, hγ, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  rw [heq]
  exact isOpen_biUnion fun γ _ => (isOpen_cell X ho hN hNO).preimage (continuous_lact _)

end GlobalTheory.SatOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsomOfGramEq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MajNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (M *ᵥ a) (M *ᵥ b) = ∑ i, ∑ j, a i * gram τ G M i j * conj (b j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  have h : ∀ (f : Fin r → Fin r → Fin r → Fin r → ℂ),
      ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ k, ∑ l, ∑ i, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h (fun k l i j => M k i * a i * τ (G k l) * (conj (M l j) * conj (b j)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring


omit [NumberField E] [IsCMField E] in
theorem isom_of_gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {M N : Matrix (Fin r) (Fin r) ℂ} (hN : N.det ≠ 0) (h : gram τ G M = gram τ G N)
    (u v : Fin r → ℂ) :
    hermC τ G ((M * N⁻¹) *ᵥ u) ((M * N⁻¹) *ᵥ v) = hermC τ G u v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hermC_mulVec, h, ← hermC_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hN),
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem col_mul {r : ℕ} (g M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * M) a = g *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [NumberField E] [IsCMField E] in
theorem gram_isom {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {g : Matrix (Fin r) (Fin r) ℂ} (hg : ∀ u v, hermC τ G (g *ᵥ u) (g *ᵥ v) = hermC τ G u v)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (g * M) = gram τ G M := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

theorem maj_isom {r : ℕ} (X : Data E r) (τ : X.Ψ) {x y : Frame X.Ψ r}
    {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : ∀ u v, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ v) = hermC τ.1 X.Gm u v)
    (hxy : mat y τ = g * mat x τ) (v : Fin r → ℂ) :
    X.maj y τ (g *ᵥ v) = X.maj x τ v := by
  simp only [Data.maj, Data.posPart, Data.gramPos, hxy, gram_isom τ.1 X.Gm hg, col_mul, hg]

theorem mat_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x z) τ = mat x τ * mat (nmat X z) τ := rfl

theorem continuous_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b =>
    (IW.cpt_entry_cd X x τ a b).continuous

theorem maj_near_orth :
    (∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (cpt X x z) τ v ∧ X.maj (cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) := by
  intro H r X ε hε
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hd : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  have ht : Filter.Tendsto (cpt X (x0F X)) (𝓝 0) (𝓝 (x0F X)) := by
    have := (continuous_cpt X (x0F X)).tendsto 0
    rwa [IW.cpt_zero] at this
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (H r X _ hd ε hε))
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun x hx z hz => ?_⟩
  obtain ⟨hz0, hm⟩ := hb (y := z) (by rw [dist_zero_right]; exact hz.trans_le (min_le_left _ _))
  have hxd : x ∈ X.dom := IW.orth_mem_dom X _ hx
  have hiso : ∀ τ : X.Ψ, ∀ u v, hermC τ.1 X.Gm ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ u)
      ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ v) = hermC τ.1 X.Gm u v := fun τ =>
    isom_of_gram_eq τ.1 X.Gm (hd τ).1 ((hx τ).trans (ho τ).symm)
  have h1 : ∀ τ : X.Ψ, mat x τ = (mat x τ * (mat (x0F X) τ)⁻¹) * mat (x0F X) τ := fun τ => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit (hd τ).1), Matrix.mul_one]
  have h2 : ∀ τ : X.Ψ, mat (cpt X x z) τ =
      (mat x τ * (mat (x0F X) τ)⁻¹) * mat (cpt X (x0F X) z) τ := fun τ => by
    rw [mat_cpt, mat_cpt, ← Matrix.mul_assoc, ← h1]
  have hdet : ∀ τ : X.Ψ, (mat x τ * (mat (x0F X) τ)⁻¹).det ≠ 0 := fun τ h0 => by
    have := (hxd τ).1
    rw [h1, Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ v => ?_⟩
  · rw [h2, Matrix.det_mul]
    exact mul_ne_zero (hdet τ) (hz0 τ).1
  · have := (hz0 τ).2 i
    simp only [dmin] at this ⊢
    rwa [h2, gram_isom τ.1 X.Gm (hiso τ)]
  · obtain ⟨w, rfl⟩ : ∃ w, v = (mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ w :=
      ⟨(mat x τ * (mat (x0F X) τ)⁻¹)⁻¹ *ᵥ v, by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mulVec]⟩
    rw [maj_isom X τ (hiso τ) (h1 τ), maj_isom X τ (hiso τ) (h2 τ)]
    exact hm τ w

end GlobalTheory.MajNear
end

