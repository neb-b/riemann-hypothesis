module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsUpqSubmatrix
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameSumBound

def swapIdx {r p : ℕ} (hp : p ≤ r) : Fin (r - p) ⊕ Fin p ≃ Fin r :=
  ((Equiv.sumComm _ _).trans finSumFinEquiv).trans (finCongr (by omega))

theorem swapIdx_inr {r p : ℕ} (hp : p ≤ r) (a : Fin p) :
    swapIdx hp (Sum.inr a) = Fin.castLE hp a := by
  ext; simp [swapIdx]

theorem swapIdx_inl_val {r p : ℕ} (hp : p ≤ r) (a : Fin (r - p)) :
    ((swapIdx hp (Sum.inl a) : Fin r) : ℕ) = p + a := by
  simp [swapIdx]

theorem sgn_submatrix {r p : ℕ} (hp : p ≤ r) :
    (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)).submatrix (swapIdx hp) (swapIdx hp) =
      -Jf (r - p) p := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j
    · subst h; simp [Jf, swapIdx_inl_val, sgn]
    · simp [Jf, h, Matrix.one_apply_ne h]
  · simp [Jf]
  · simp [Jf]
  · by_cases h : i = j
    · subst h; simp [Jf, swapIdx_inr, sgn]
    · simp [Jf, h, Matrix.one_apply_ne h]

theorem isUpq_submatrix {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : gᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * g.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    IsUpq (g.submatrix (swapIdx hp) (swapIdx hp)) := by
  set J : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ) with hJ
  have hJT : Jᵀ = J := Matrix.diagonal_transpose _
  have h1 : gᴴ * J * g = J := by
    have := congrArg Matrix.transpose hg
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJT,
      ← Matrix.mul_assoc] at this
    exact this
  have h2 : Jf (r - p) p = -(J.submatrix (swapIdx hp) (swapIdx hp)) := by
    rw [hJ, sgn_submatrix, neg_neg]
  unfold IsUpq
  rw [h2, Matrix.conjTranspose_submatrix, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isOrth_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ, hx τ]

theorem isUpq_frame {r : ℕ} (X : Data E r) {x0 y : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hy : IsOrth X y) (τ : X.Ψ) :
    IsUpq (((mat x0 τ)⁻¹ * mat y τ).submatrix (swapIdx X.p0_le) (swapIdx X.p0_le)) := by
  apply isUpq_submatrix
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
  have h := hy τ
  conv_lhs at h => rw [← Matrix.mul_nonsing_inv_cancel_left (mat x0 τ) (mat y τ) hu]
  rw [FrameDegreeData.gram_mul, h0 τ] at h
  exact h

theorem quot_eq {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0) (hx : IsOrth X x)
    (γ δ : GL (Fin r) E) (τ : X.Ψ) :
    ((mat x0 τ)⁻¹ * mat (lact δ x) τ) * ((mat x0 τ)⁻¹ * mat (lact γ x) τ)⁻¹ =
      (mat x0 τ)⁻¹ * ((δ * γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ := by
  have hu0 : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X hx τ)
  have e1 : ∀ γ : GL (Fin r) E,
      mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := fun _ => rfl
  have hγ : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero τ.1) (map_one τ.1)]
  have hinv : ((mat x0 τ)⁻¹ * mat (lact γ x) τ)⁻¹ =
      (mat x τ)⁻¹ * (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ) := by
    apply Matrix.inv_eq_left_inv
    rw [e1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu0, ← Matrix.mul_assoc _ _ (mat x τ), hγ,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hu]
  rw [hinv, e1, Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu]

theorem frame_sum_bound :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r), c ≤ ‖((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1) a b‖) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < s → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal ((∏ τ : X.Ψ, ‖dmin X.Gm (lact γ.1 x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (lact γ.1 x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ^ s) ≤ C) := by
  intro hsep r X x0 h0 hPD s hs
  obtain ⟨c, hc, hcs⟩ := hsep r X x0 h0 hPD
  have hr : r - X.p0 + X.p0 = r := Nat.sub_add_cancel X.p0_le
  obtain ⟨C, hC, hb⟩ := sumBd_sum (p := r - X.p0) (q := X.p0) (f := X.Ψ.card) (s := s)
    (by rw [hr]; exact hs) hc
  refine ⟨C, hC, fun x hx => ?_⟩
  let eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm
  have key := hb X.Γ (fun γ k => ((mat x0 (eΨ k))⁻¹ * mat (lact γ.1 x) (eΨ k)).submatrix
      (swapIdx X.p0_le) (swapIdx X.p0_le))
    (fun γ k => isUpq_frame X h0 (isOrth_lact X γ.2 hx) _)
    (fun γ δ hne => by
      have hmem : δ.1 * γ.1⁻¹ ∈ X.Γ := X.Γ.mul_mem δ.2 (X.Γ.inv_mem γ.2)
      have hne1 : δ.1 * γ.1⁻¹ ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h).symm)
      obtain ⟨τ, a, b, hab⟩ := hcs _ hmem hne1
      refine ⟨eΨ.symm τ, (swapIdx X.p0_le).symm a, (swapIdx X.p0_le).symm b, ?_⟩
      rw [Equiv.apply_symm_apply, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
        quot_eq X h0 hx, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [Matrix.sub_apply] at hab
      convert hab using 3
      simp [Matrix.one_apply])
  refine le_trans (le_of_eq ?_) key
  refine tsum_congr fun γ => ?_
  congr 1
  rw [← Real.finsetProd_rpow _ _ (fun τ _ => by positivity) s, ← eΨ.prod_comp]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [IC.norm_dmin_orth X (isOrth_lact X γ.2 hx), one_div, Complex.normSq_eq_norm_sq]
  have hm : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      lminor M (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) =
        (M.submatrix (swapIdx X.p0_le) (swapIdx X.p0_le)).toBlocks₂₂.det := fun M => by
    unfold lminor
    congr 1
  rw [hm]

end GlobalTheory.FrameSumBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaFrameOfDelta
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

private theorem lact_rmul_torus_haar_measure {r : ℕ} {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat y τ) (mat b τ)).symm

theorem kaFrame_of_delta {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (hbb : 0 < bb)
    (δ : Frame X.Ψ r → ℝ) (h0 : ∀ x, 0 ≤ δ x) (hm : Measurable δ)
    (hpos : ∀ x ∈ X.dom, 0 < δ x ∧ δ x ≤ 1)
    (hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, δ (rmul x b) = δ x)
    (hch : ∀ z ∈ OmF X x0, δ (cpt X x0 z) = Real.exp (-rhF X x0 z))
    (hloc : ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → δ (cpt X x z) ≤ C * δ x)
    (hsum : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (δ (lact γ.1 x) ^ (bb / 2)) ≤ C) :
    ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧
      (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom,
        ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧
      ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x := by
  have hb0 : 0 ≤ bb := hbb.le
  refine ⟨fun x => δ x ^ bb, hm.pow_const bb, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hpos x hx
    exact ⟨Real.rpow_pos_of_pos h1 bb, Real.rpow_le_one h1.le h2 hb0⟩
  · intro x hx b hb
    show δ (rmul x b) ^ bb = δ x ^ bb
    rw [hinv x hx b hb]
  · intro z hz
    show δ (cpt X x0 z) ^ bb = kaF X x0 bb z
    rw [hch z hz, kaF, ← Real.exp_mul]
    congr 1
    ring
  · obtain ⟨C, hC, hCb⟩ := hsum
    refine ⟨C, hC, fun x hx => ?_⟩
    obtain ⟨x1, hx1, b, hb, rfl⟩ := (ortho_holds (E := E)) r X x hx
    have hd1 : x1 ∈ X.dom := IC.orth_mem_dom X hx1
    calc ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (δ (lact γ.1 (rmul x1 b)) ^ bb))
        = ∑' γ : X.Γ, ENNReal.ofReal (δ (lact γ.1 x1) ^ (bb / 2)) := by
          refine tsum_congr fun γ => ?_
          rw [lact_rmul_torus_haar_measure, hinv _ (OntoS.dom_lact X γ.2 hd1) b hb, Real.sqrt_eq_rpow,
            ← Real.rpow_mul (h0 _), show bb / 2 = bb * (1 / 2) by ring]
      _ ≤ C := hCb x1 hx1
  · obtain ⟨ρ, C, hρ, hC⟩ := hloc
    refine ⟨ρ, max C 0 ^ bb, hρ, fun x hx z hz => ?_⟩
    have h1 : δ (cpt X x z) ≤ max C 0 * δ x :=
      (hC x hx z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (h0 x))
    show δ (cpt X x z) ^ bb ≤ max C 0 ^ bb * δ x ^ bb
    calc δ (cpt X x z) ^ bb ≤ (max C 0 * δ x) ^ bb := Real.rpow_le_rpow (h0 _) h1 hb0
      _ = max C 0 ^ bb * δ x ^ bb := Real.mul_rpow (le_max_right _ _) (h0 x)

theorem kaFrame : (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → Measurable (fun x : Frame X.Ψ r => (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ (∀ x ∈ X.dom, 0 < (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ∧ (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (∏ τ : X.Ψ, ‖dmin X.Gm (rmul x b) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ ∀ z ∈ OmF X x0, (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x0 z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = Real.exp (-rhF X x0 z)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ C * (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < s → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal ((∏ τ : X.Ψ, ‖dmin X.Gm (lact γ.1 x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (lact γ.1 x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ^ s) ≤ C) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) := by
  intro hM hL hS r X x0 hx0 hpd bb hbb
  obtain ⟨h1, h2, h3, h4⟩ := hM r X x0 hx0
  have hc : 0 ≤ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
  refine kaFrame_of_delta X x0 bb (by linarith) _ (fun x => Finset.prod_nonneg fun τ _ => by positivity)
    h1 h2 h3 h4 (hL r X x0 hx0) (hS r X x0 hx0 hpd (bb / 2) (by linarith))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.MinorRatioNear

noncomputable abbrev sgnMat (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sgnMat_mul_self (r p : ℕ) : sgnMat r p * sgnMat r p = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem sgnMat_map_conj (r p : ℕ) : (sgnMat r p).map (starRingEnd ℂ) = sgnMat r p := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.diagonal_apply, h]

theorem mul_sgnMat_mul_conjTranspose {r p : ℕ} {g : Matrix (Fin r) (Fin r) ℂ}
    (h : gᵀ * sgnMat r p * g.map (starRingEnd ℂ) = sgnMat r p) :
    g * sgnMat r p * gᴴ = sgnMat r p := by
  have h1 : gᴴ * sgnMat r p * g = sgnMat r p := by
    have := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h
    simp only [Matrix.map_mul, sgnMat_map_conj] at this
    have e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g := by ext a b; simp
    rw [e] at this
    exact this
  have h2 : (sgnMat r p * gᴴ * sgnMat r p) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, sgnMat_mul_self]
  have h3 : g * (sgnMat r p * gᴴ * sgnMat r p) = 1 := mul_eq_one_comm.1 h2
  calc g * sgnMat r p * gᴴ = g * (sgnMat r p * gᴴ * sgnMat r p) * sgnMat r p := by
        simp only [Matrix.mul_assoc, sgnMat_mul_self, Matrix.mul_one]
    _ = sgnMat r p := by rw [h3, Matrix.one_mul]

theorem signed_sum_rows {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) (v : Fin p → ℂ) :
    ∑ a : Fin r, sgn p a * ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  set R : Matrix (Fin p) (Fin r) ℂ := g.submatrix (Fin.castLE hp) id with hR
  have hRR : R * sgnMat r p * Rᴴ = 1 := by
    have : R * sgnMat r p * Rᴴ =
        (g * sgnMat r p * gᴴ).submatrix (Fin.castLE hp) (Fin.castLE hp) := by
      ext i j
      simp [hR, Matrix.mul_apply]
    rw [this, h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [sgn]
  have key : ((v ᵥ* R) ᵥ* sgnMat r p) ⬝ᵥ star (v ᵥ* R) = v ⬝ᵥ star v := by
    rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, hRR, Matrix.vecMul_one]
  apply Complex.ofReal_injective
  push_cast
  simp only [dotProduct, Matrix.vecMul_diagonal, Pi.star_apply, Complex.star_def] at key
  convert key using 2 with a _ i _
  · rw [mul_comm ((v ᵥ* R) a), mul_assoc, Complex.mul_conj']
  · rw [Complex.mul_conj']

theorem neg_sum_rows {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) (v : Fin p → ℂ) :
    ∑ i, ‖v i‖ ^ 2 + ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
        ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 =
      ∑ i : Fin p, ‖(v ᵥ* g.submatrix (Fin.castLE hp) (Fin.castLE hp)) i‖ ^ 2 := by
  rw [← signed_sum_rows hp h v,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin r => (a : ℕ) < p), add_assoc,
    ← Finset.sum_add_distrib]
  have e0 : ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
      (sgn p a * ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 +
        ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    have := (Finset.mem_filter.1 ha).2
    simp [sgn, this]
  rw [e0, add_zero]
  symm
  refine Finset.sum_bij (fun i _ => Fin.castLE hp i) (fun i _ => by simp)
    (fun i _ j _ hij => Fin.castLE_injective _ hij) (fun a ha => ?_) (fun i _ => ?_)
  · exact ⟨⟨a, (Finset.mem_filter.1 ha).2⟩, Finset.mem_univ _, rfl⟩
  · simp [sgn, Matrix.vecMul, dotProduct]

theorem det_block_ne_zero {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) :
    (g.submatrix (Fin.castLE hp) (Fin.castLE hp)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have := neg_sum_rows hp h v
  rw [hv0] at this
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at this
  have h1 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
      ‖(v ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : ∑ i, ‖v i‖ ^ 2 = 0 := by linarith
  apply hv
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 h3 i (Finset.mem_univ _)
  simpa using this

theorem norm_entry_le_one {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) (i : Fin p) (a : Fin r) :
    ‖((g.submatrix (Fin.castLE hp) (Fin.castLE hp))⁻¹ * g.submatrix (Fin.castLE hp) id) i a‖ ≤ 1 := by
  set A := g.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  have hu : IsUnit A.det := (det_block_ne_zero hp h).isUnit
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hu
  by_cases ha : (a : ℕ) < p
  · have : (A⁻¹ * g.submatrix (Fin.castLE hp) id) i a = (A⁻¹ * A) i ⟨a, ha⟩ := rfl
    rw [this, hinv, Matrix.one_apply]
    split_ifs <;> simp
  · have hs := neg_sum_rows hp h (A⁻¹ i)
    have e1 : ∀ j, (A⁻¹ i ᵥ* A) j = (1 : Matrix (Fin p) (Fin p) ℂ) i j := fun j => by
      rw [← hinv]; rfl
    rw [← hA] at hs
    have e2 : ∑ j : Fin p, ‖(A⁻¹ i ᵥ* A) j‖ ^ 2 = 1 := by
      simp only [e1]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Matrix.one_apply_ne hj.symm]
      · simp
    have h2 : 0 ≤ ∑ j, ‖A⁻¹ i j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have h3 : ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin r => ¬ (a : ℕ) < p),
        ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2)
        (fun _ _ => by positivity) (by simpa using ha)
    have h4 : ‖(A⁻¹ i ᵥ* g.submatrix (Fin.castLE hp) id) a‖ ^ 2 ≤ 1 := by linarith
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h4

theorem exists_det_near_one (p : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ N : Matrix (Fin p) (Fin p) ℂ,
    (∀ i j, ‖(N - 1) i j‖ < δ) → 1 / 2 ≤ ‖N.det‖ := by
  have hc : Continuous fun N : Fin p → Fin p → ℂ => ‖(Matrix.of N).det‖ :=
    (Continuous.matrix_det (A := fun N : Fin p → Fin p → ℂ => Matrix.of N) continuous_id).norm
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1
    (hc.continuousAt (x := fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun N hN => ?_⟩
  have := @H (fun i j => N i j) (by
    rw [dist_pi_lt_iff hδ]; intro i
    rw [dist_pi_lt_iff hδ]; intro j
    rw [dist_eq_norm]; exact hN i j)
  have e : (Matrix.of fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j).det = 1 := Matrix.det_one
  rw [e, norm_one, Real.dist_eq, abs_lt] at this
  have e' : (Matrix.of fun i j => N i j) = N := rfl
  rw [e'] at this
  linarith [this.1]

theorem exists_block_det_ge {r p : ℕ} (hp : p ≤ r) : ∃ δ : ℝ, 0 < δ ∧
    ∀ g n : Matrix (Fin r) (Fin r) ℂ, g * sgnMat r p * gᴴ = sgnMat r p →
      (∀ a b, ‖(n - 1) a b‖ ≤ δ) →
      ‖(g.submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ / 2 ≤
        ‖((g * n).submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ := by
  obtain ⟨δ, hδ, H⟩ := exists_det_near_one p
  refine ⟨δ / (r + 1), by positivity, fun g n h hn => ?_⟩
  set A := g.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  set R := g.submatrix (Fin.castLE hp) (id : Fin r → Fin r) with hR
  have hu : IsUnit A.det := (det_block_ne_zero hp h).isUnit
  have e1 : (g * n).submatrix (Fin.castLE hp) (Fin.castLE hp) =
      A * (A⁻¹ * R * n.submatrix id (Fin.castLE hp)) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rfl
  have e2 : R * (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) = A := by
    have : R * (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) =
        (g * 1).submatrix (Fin.castLE hp) (Fin.castLE hp) := rfl
    rw [this, Matrix.mul_one]
  have e3 : A⁻¹ * R * n.submatrix id (Fin.castLE hp) - 1 =
      A⁻¹ * R * (n - 1).submatrix id (Fin.castLE hp) := by
    have : (n - 1).submatrix id (Fin.castLE hp) = n.submatrix id (Fin.castLE hp) -
        (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) := rfl
    rw [this, Matrix.mul_sub, Matrix.mul_assoc A⁻¹ R (Matrix.submatrix 1 _ _), e2,
      Matrix.nonsing_inv_mul _ hu]
  have h1 := H (A⁻¹ * R * n.submatrix id (Fin.castLE hp)) fun i j => by
    rw [e3, Matrix.mul_apply]
    calc ‖∑ a, (A⁻¹ * R) i a * (n - 1).submatrix id (Fin.castLE hp) a j‖
        ≤ ∑ a : Fin r, δ / (r + 1) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          rw [norm_mul]
          calc _ ≤ 1 * (δ / (r + 1)) :=
                mul_le_mul (norm_entry_le_one hp h i a) (hn _ _) (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ < δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_div_assoc, div_lt_iff₀ (by positivity)]
          nlinarith
  rw [e1, Matrix.det_mul, norm_mul]
  nlinarith [norm_nonneg A.det]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_nmat_sub_one_le {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖(mat (nmat X z) τ - 1) a b‖ ≤ ‖z‖ := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  simp only [mat, nmat, Matrix.of_apply]
  by_cases h : b < a
  · rw [dite_eq_left h, if_neg h.ne', sub_zero]
    exact PiLp.norm_apply_le z _
  · rw [dite_eq_right h, sub_self, norm_zero]
    exact norm_nonneg _

theorem isometry_of_orth {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) :
    ((mat x0 τ)⁻¹ * mat x τ) * sgnMat r X.p0 * ((mat x0 τ)⁻¹ * mat x τ)ᴴ = sgnMat r X.p0 := by
  apply mul_sgnMat_mul_conjTranspose
  have hu : IsUnit (mat x0 τ).det := (ExF.det_ne_of_orth X h0 τ).isUnit
  have := FrameDegreeData.gram_mul τ.1 X.Gm (mat x0 τ) ((mat x0 τ)⁻¹ * mat x τ)
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, hx τ, h0 τ] at this
  exact this.symm

theorem dmin_cpt_eq {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x z) τ i = dmin X.Gm (cpt X x0 z) τ i := by
  unfold dmin
  rw [ExF.mat_cpt, ExF.mat_cpt, FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, hx τ, h0 τ]

theorem minorRatio_near :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ C * (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) := by
  intro r X x0 h0
  set i0 : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ with hi0
  obtain ⟨δ, hδ, H⟩ := exists_block_det_ge X.p0_le
  have hc : Continuous fun z : V (nd X) => fun τ : X.Ψ => dmin X.Gm (cpt X x0 z) τ i0 :=
    continuous_pi fun τ => (ExtFPf.cont_dmin X τ i0).comp (FundSetPf.cont_cpt (X := X) (x0 := x0))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V (nd X)) δ).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨δ, ∏ _τ : X.Ψ, (4 * B), hδ, fun x hx z hz => ?_⟩
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun τ _ => by positivity) fun τ _ => ?_
  have hiso := isometry_of_orth X h0 hx τ
  have h1 : ‖dmin X.Gm (cpt X x z) τ i0‖ ≤ B := by
    rw [dmin_cpt_eq X h0 hx]
    exact (norm_le_pi_norm (fun τ : X.Ψ => dmin X.Gm (cpt X x0 z) τ i0) τ).trans
      (hB z (by simpa using hz.le))
  have h2 : ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i0‖ / 2 ≤
      ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x z) τ) i0‖ := by
    rw [ExF.mat_cpt, ← Matrix.mul_assoc]
    exact H _ _ hiso fun a b => (norm_nmat_sub_one_le X z τ a b).trans hz.le
  have h3 : 0 < ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i0‖ :=
    norm_pos_iff.2 (det_block_ne_zero X.p0_le hiso)
  rw [IC.norm_dmin_orth X hx]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
  calc _ ≤ B / (‖lminor ((mat x0 τ)⁻¹ * mat x τ) i0‖ / 2) ^ 2 := by gcongr
    _ = _ := by field_simp; norm_num

end GlobalTheory.MinorRatioNear
end

