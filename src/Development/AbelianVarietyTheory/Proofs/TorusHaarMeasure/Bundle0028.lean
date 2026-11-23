module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousInvLeadingBlockEntry
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimum
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitaryStab_mul_compact_of_le_firstMinimum :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  intro r X H hH x0 hx0 ε hε
  obtain ⟨-, -, hfr⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hιc, -, hιg⟩ := hfr x0 hx0
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_bound_orthonormal_frame_mahler r X ε hε
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  refine ⟨ι '' {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R},
    (GlobalTheory.FinCovol.isCompact_orth_bounded r X R).image_of_continuousOn
      (hιc.mono fun x hx => hx.1), fun g hg => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := hR _ (horth g) hg
  obtain ⟨u, hu⟩ := exists_unitary_elem_of_isUStab r X H hH γ hγ
  have huΓ : u ∈ Γ := (hΓ u).2 ⟨γ, hγ, hu⟩
  refine ⟨u⁻¹, (hΓ _).1 (Γ.inv_mem huΓ), u * g, ⟨_, ⟨horth (u * g), ?_⟩, hιg (u * g)⟩,
    (inv_mul_cancel_left u g).symm⟩
  have key : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) x0 = lact γ (X.lmulC (fun τ =>
        (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
    funext τ
    change (((u : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) * mat x0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ)
    rw [hu, Matrix.mul_assoc]
  rw [key]
  exact hb

end GlobalTheory.FiniteCovolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtLogMinorProd
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PotentialTransfer

open Filter Matrix GlobalTheory.SharpGradient GlobalTheory.Up
open scoped ComplexOrder ComplexConjugate

section Matrices

variable {n p : ℕ}

def topT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ

def lowT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  Matrix.of fun a k => if (k : ℕ) < p then 0 else g k (Fin.castLE h a)

noncomputable def graphT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  (topT h g)⁻¹ * lowT h g

theorem leading_gram (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) :
    (gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      g.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ := by
  ext a b
  have e2 : (topT h g * (topT h g)ᴴ) a b = ∑ k : Fin n, if (k : ℕ) < p then
      g k (Fin.castLE h a) * starRingEnd ℂ (g k (Fin.castLE h b)) else 0 := by
    rw [Matrix.mul_apply]
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
      (fun k => ?_)
    · rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · simp [topT, Matrix.conjTranspose_apply]
  rw [Matrix.sub_apply, e2, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  by_cases hk : (k : ℕ) < p
  · simp [lowT, sgn, hk, Matrix.conjTranspose_apply]
  · simp [lowT, sgn, hk, Matrix.conjTranspose_apply]

theorem one_sub_graph (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) (hd : (topT h g).det ≠ 0) :
    1 - graphT h g * (graphT h g)ᴴ =
      (topT h g)⁻¹ * (topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ) * ((topT h g)⁻¹)ᴴ := by
  have hu : IsUnit (topT h g).det := isUnit_iff_ne_zero.2 hd
  have h1 : (topT h g)⁻¹ * topT h g = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : (topT h g)ᴴ * ((topT h g)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul, h2, graphT,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem graph_posDef (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) (hd : (topT h g).det ≠ 0)
    (hP : (topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ).PosDef) :
    (1 - graphT h g * (graphT h g)ᴴ).PosDef ∧
      (1 - graphT h g * (graphT h g)ᴴ).det.re =
        ‖(topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ).det‖ / ‖(topT h g).det‖ ^ 2 := by
  have hu : IsUnit (topT h g)⁻¹ := by
    rw [Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.2 hd
  have hpd : (1 - graphT h g * (graphT h g)ᴴ).PosDef := by
    rw [one_sub_graph h g hd]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).2 hP
  refine ⟨hpd, ?_⟩
  rw [← ExF.norm_of_pos hpd.det_pos, one_sub_graph h g hd, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_mul, norm_mul,
    norm_star, norm_inv]
  have : ‖(topT h g).det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  field_simp

theorem contDiffAt_graph {m : ℕ} (h : p ≤ n) {g : V m → Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ a b, ContDiff ℂ ∞ fun y => g y a b) {z : V m} (hd : (topT h (g z)).det ≠ 0)
    (a : Fin p) (k : Fin n) : ContDiffAt ℂ ∞ (fun y => graphT h (g y) a k) z := by
  have ht : ∀ i j, ContDiff ℂ ∞ fun y => topT h (g y) i j := fun i j => hg _ _
  have e : (fun y => graphT h (g y) a k) = fun y => ∑ b, (((topT h (g y)).det)⁻¹ *
      ((topT h (g y)).updateRow b (Pi.single a 1)).det) * lowT h (g y) b k := by
    funext y
    simp [graphT, Matrix.inv_def, Matrix.mul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine ContDiffAt.sum fun b _ => ContDiffAt.mul (ContDiffAt.mul ?_ ?_) ?_
  · exact (ExhD.contDiff_det_of ht).contDiffAt.inv hd
  · refine (ExhD.contDiff_det_of fun i j => ?_).contDiffAt
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact ht _ _
  · simp only [lowT, Matrix.of_apply]
    split_ifs
    · exact contDiffAt_const
    · exact (hg _ _).contDiffAt

end Matrices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x1 x2 x : Frame X.Ψ r}

theorem det_topT_ne_zero (h2 : IsOrth X x2) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ)).det ≠ 0 := by
  rw [topT, Matrix.det_transpose]
  exact lminor_inv_mul_ne_zero h2 hx τ

theorem gramPos_eq (h2 : IsOrth X x2) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.gramPos x τ = topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) * (topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ -
      lowT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) * (lowT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ := by
  have hu : IsUnit (mat x2 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x2 h2 τ)
  rw [← leading_gram, ← h2 τ, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rfl

theorem graph_posDef_of_mem (h2 : IsOrth X x2) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (1 - graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) *
      (graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ).PosDef :=
  (graph_posDef _ _ (det_topT_ne_zero h2 hx τ) (gramPos_eq h2 x τ ▸ X.gramPos_posDef hx τ)).1

theorem rhX_eq_sum_graph (h2 : IsOrth X x2) (hx : x ∈ X.dom) :
    rhX X x2 x = ∑ τ, -Real.log (1 - graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) *
      (graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ).det.re := by
  rw [rhX_eq_sum_log h2 hx]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [(graph_posDef _ _ (det_topT_ne_zero h2 hx τ) (gramPos_eq h2 x τ ▸ X.gramPos_posDef hx τ)).2,
    ← gramPos_eq h2 x τ, topT, Matrix.det_transpose]
  rfl

theorem contDiff_inv_mul_cpt (x1 x2 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun y : V (nd X) => ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ) a b := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun c _ => contDiff_const.mul (OntoB.cd_cpt_entry X x1 τ c b)

noncomputable def minorProd (X : Data E r) (x1 x2 : Frame X.Ψ r) (y : V (nd X)) : ℂ :=
  ∏ τ, lminor ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩

theorem contDiff_minorProd (x1 x2 : Frame X.Ψ r) : ContDiff ℂ ∞ (minorProd X x1 x2) :=
  contDiff_prod fun τ _ => ExhD.contDiff_det_of fun _ _ => contDiff_inv_mul_cpt x1 x2 τ _ _

theorem minorProd_ne_zero (h2 : IsOrth X x2) {y : V (nd X)} (hy : y ∈ OmF X x1) :
    minorProd X x1 x2 y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => lminor_inv_mul_ne_zero h2 hy τ

theorem rhX_cpt_eq_add (h2 : IsOrth X x2) {y : V (nd X)} (hy : y ∈ OmF X x1) :
    rhX X x2 (cpt X x1 y) = rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) := by
  rw [rhX_eq_sum h2 hy, minorProd, map_prod, Real.log_prod fun τ _ =>
    (Complex.normSq_pos.2 (lminor_inv_mul_ne_zero h2 hy τ)).ne']
  simp only [Complex.normSq_eq_norm_sq]
  rfl

theorem contDiffAt_log_minorProd (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Complex.normSq (minorProd X x1 x2 y))) z := by
  have hn : ContDiff ℝ ∞ fun y : V (nd X) => Complex.normSq (minorProd X x1 x2 y) := by
    simp only [Complex.normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp ((contDiff_minorProd x1 x2).restrict_scalars ℝ)
  exact (Real.contDiffAt_log.2 (Complex.normSq_pos.2 (minorProd_ne_zero h2 hz)).ne').comp z
    hn.contDiffAt

theorem rhX_cpt_eventuallyEq (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    (fun y => rhX X x2 (cpt X x1 y)) =ᶠ[𝓝 z]
      fun y => rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) := by
  filter_upwards [(OntoB.isOpen_OmF X x1).mem_nhds hz] with y hy
  exact rhX_cpt_eq_add h2 hy

theorem contDiffAt_rhX_cpt (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    ContDiffAt ℝ ∞ (fun y => rhX X x2 (cpt X x1 y)) z :=
  ((OntoB.rhF_contDiffAt hz).add (contDiffAt_log_minorProd h2 hz)).congr_of_eventuallyEq
    (rhX_cpt_eventuallyEq h2 hz)

theorem leviO_rhX (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) (ξ : Fin (nd X) → ℂ) :
    leviO X x1 (rhX X x2) z ξ = leviRh X x1 z ξ := by
  have e : (fun y => ((rhX X x2 (cpt X x1 y) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun y => ((rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) : ℝ) : ℂ) := by
    filter_upwards [rhX_cpt_eventuallyEq h2 hz] with y hy
    rw [hy]
  unfold leviO leviM leviRh
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add
      ((OntoB.rhF_contDiffAt hz).of_le ExhE.two_le_infty)
      ((contDiffAt_log_minorProd h2 hz).of_le ExhE.two_le_infty) ξ,
    ExF.levi_logNormSq_zero _ (contDiff_minorProd x1 x2) z (minorProd_ne_zero h2 hz) ξ, add_zero]

theorem sharpAt_rhX_cpt (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (ξ : Fin (nd X) → ℂ) : SharpAt (fun y => rhX X x2 (cpt X x1 y)) z ξ := by
  choose U hU he using fun τ => exists_unitary_rows (graph_posDef_of_mem h2 hz τ)
  have hS : SharpAt (fun y => ∑ τ, ∑ a, -Real.log (1 - ∑ b, Complex.normSq
      (((U τ)ᴴ * graphT X.p0_le ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ)) a b))) z ξ := by
    refine sharpAt_sum' fun τ => sharpAt_sum fun a => ?_
    refine sharpAt_ball
      (g := fun b y => ((U τ)ᴴ * graphT X.p0_le ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ)) a b) ξ
      (fun b => ?_) (row_lt_one _ (hU τ) (graph_posDef_of_mem h2 hz τ) a)
    simp only [Matrix.mul_apply]
    exact (ContDiffAt.sum fun c _ => contDiffAt_const.mul
      (contDiffAt_graph X.p0_le (contDiff_inv_mul_cpt x1 x2 τ) (det_topT_ne_zero h2 hz τ) c b)).of_le
      ExhE.two_le_infty
  refine hS.of_minorant ((contDiffAt_rhX_cpt h2 hz).of_le ExhE.two_le_infty) ?_ ?_
  · filter_upwards [(OntoB.isOpen_OmF X x1).mem_nhds hz] with y hy
    rw [rhX_eq_sum_graph h2 hy]
    exact Finset.sum_le_sum fun τ _ => rows_le_neg_log_det _ (hU τ) (graph_posDef_of_mem h2 hy τ)
  · rw [rhX_eq_sum_graph h2 hz]
    exact Finset.sum_congr rfl fun τ _ => he τ

theorem potential_transfer : RhTr (E := E) := by
  intro r X x1 x2 _ h2
  refine ⟨fun z hz => (contDiffAt_rhX_cpt h2 hz).contDiffWithinAt, fun z hz =>
    ⟨rhX_nonneg h2 hz, fun ξ => ⟨leviO_rhX h2 hz ξ, ?_⟩⟩⟩
  rw [← leviO_rhX h2 hz ξ]
  exact (sharpAt_rhX_cpt h2 hz ξ).2.2.2

end GlobalTheory.PotentialTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurablePhi
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivInFFPf

open Filter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem muF_lt_top (hM : MeasInvStatement (E := E)) (hfin : FinMu X) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) : muF X x0 FF < ⊤ := by
  classical
  obtain ⟨x1, ho1, F1, hF1, hlt⟩ := hfin
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hle
  let S : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X ho1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
  have hψ : Measurable (Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) := measurable_one.indicator hS.compl
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Sᶜ.indicator 1 x := by
    intro x _ b hb
    have : rmul x b ∈ S ↔ x ∈ S := by
      simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
        GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
    simp only [Set.indicator, Set.mem_compl_iff, this, Pi.one_apply]
  have h0 : ∫⁻ z, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ hψ hB]
    refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
    filter_upwards [hF1.2.2.2] with z hz
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 ((hSiff _).2 hz)) _
  have hae := (lintegral_eq_zero_iff (hψ.comp (FundSetPf.cont_cpt X x0).measurable)).1 h0
  refine lt_of_le_of_lt (measure_mono_ae ?_) (hle.trans_lt hlt)
  filter_upwards [hae] with z hz hzF
  refine ⟨hzF, (hSiff _).1 ?_⟩
  by_contra hn
  have : Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) = 0 := hz
  rw [Set.indicator_of_mem (show _ ∈ Sᶜ from hn)] at this
  exact one_ne_zero this

variable (Xa : ArchInM X) (Fl : FlatM X Xa)

theorem ae_exists_ne {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 → ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := by
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hn := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have hc : (⋃ j : Fin Fl.δ, ⋃ γ : GL (Fin r) E,
      {z | ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (Fl.xs j) b)}).Countable := by
    refine Set.countable_iUnion fun j => Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_
    rintro z ⟨b, hb, h⟩ z' ⟨b', hb', h'⟩
    refine FundSetPf.cpt_uniq X ho (ExtFPf.invF_mem X hb) (ExtFPf.invF_mem X hb') ?_
    rw [h, h', FundSetPf.lact_rmul, FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_assoc,
      ExtFPf.rmul_invF X hb, ExtFPf.rmul_invF X hb']
  have hac : muF X x0 ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  filter_upwards [hac.ae_le (hc.ae_notMem volume)] with z hz hzO
  by_contra hs
  push Not at hs
  obtain ⟨j, γ, -, b, hb, h⟩ := (Fl.S_eq _ hzO).1 hs
  exact hz (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨γ, b, hb, h⟩⟩)

theorem pnorm_contOn {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom :=
  hP.1.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)

theorem measurable_cut {f : Frame X.Ψ r → ℝ} (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

theorem sum_pnorm_pos {N : ℕ} {la : Wt X.Ψ r} {P : Fin N → Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : ∃ k, P k x ≠ 0) : 0 < ∑ k, X.pnorm la (P k) x ^ 2 := by
  simp only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]
  exact mul_pos (Real.exp_pos _) (sum_normSq_pos h)

theorem real_bound {e F G w s K C : ℝ} {a b : ℂ} {n : ℕ} (hn : 1 ≤ n) (he : 0 ≤ e) (hF : F = e * ‖a‖ ^ 2)
    (hG : G = e * ‖b‖ ^ 2) (hw : 0 < w) (hs : 0 ≤ s) (hK : w ≤ K * s) (hC : G ≤ C * w ^ n) :
    e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2)) ≤
      2 * |K| ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) + 2 * |K| ^ ((n : ℝ) - 1 / 2) * C := by
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hKs : 0 < K * s := hw.trans_le hK
  have hs' : 0 < s := lt_of_le_of_ne hs (by rintro rfl; simp at hKs)
  have hK0 : 0 < K := (mul_pos_iff_of_pos_right hs').1 hKs
  rw [abs_of_pos hK0]
  have h1 : s ^ (-((n : ℝ) - 1 / 2)) ≤ K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2)) := by
    have : (K * s) ^ (-((n : ℝ) - 1 / 2)) ≤ w ^ (-((n : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hw hK (by linarith)
    rw [Real.mul_rpow hK0.le hs, Real.rpow_neg hK0.le,
      inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK0 _)] at this
    exact this
  have h2 : w ^ (-(1 / 2 : ℝ)) * w ^ (-((n : ℝ) - 1 / 2)) = w ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hw]; congr 1; ring
  have h3 : e * ‖a - b‖ ^ 2 ≤ 2 * F + 2 * G := by
    have h4 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [hF, hG]
    nlinarith [mul_le_mul_of_nonneg_left h4 he]
  have h5 : G * w ^ (-(n : ℝ)) ≤ C := by
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos hw n)]
    exact hC
  have hKp := Real.rpow_pos_of_pos hK0 ((n : ℝ) - 1 / 2)
  calc e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2))
      ≤ (2 * F + 2 * G) * w ^ (-(1 / 2 : ℝ)) * (K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2))) := by
        have : 0 ≤ 2 * F + 2 * G := le_trans (by positivity) h3
        gcongr
    _ = 2 * K ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) +
          2 * K ^ ((n : ℝ) - 1 / 2) * (G * w ^ (-(n : ℝ))) := by rw [← h2]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.Up.DivInFFPf
end

