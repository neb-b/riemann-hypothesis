module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem compactSpace_unitary_of_definite :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  intro r X H hH hp
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  obtain ⟨-, -, h⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hc, -, hι⟩ := h (x0F X) hx0
  have hK := (isCompact_orth_bounded r X R).image_of_continuousOn
    (hc.mono fun x hx => hx.1)
  refine ⟨hK.of_isClosed_subset isClosed_univ fun g _ => ?_⟩
  exact ⟨_, ⟨horth g, hR _ (horth g)⟩, hι g⟩

end GlobalTheory.FinCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfDetFderivNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Filter Topology

namespace GlobalTheory.JacobianIndependence

theorem eq_zero_of_eventually_eval {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (a : EuclideanSpace ℂ (Fin n))
    (h : ∀ᶠ w in 𝓝 a, MvPolynomial.eval (fun k => w k) p = 0) : p = 0 := by
  have hc : Continuous (fun x : Fin n → ℂ => (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))) :=
    PiLp.continuous_toLp 2 _
  have h1 : ∀ᶠ x in 𝓝 (fun k => a k), MvPolynomial.eval x p = 0 :=
    (hc.tendsto (fun k => a k)).eventually h
  rw [nhds_pi, Filter.Eventually, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  refine MvPolynomial.funext_set t (fun i => infinite_of_mem_nhds _ (ht i)) ?_
  intro x hx
  rw [map_zero]
  exact hsub (fun i _ => hx i (Set.mem_univ i))

theorem eq_zero_of_det_fderiv_ne_zero :
    ∀ (n : ℕ) (f : Fin n → V n → ℂ), (∀ k, ∀ᶠ z in nhds (0 : V n), DifferentiableAt ℂ (f k) z) →
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => f k z : V n)) 0).det ≠ 0 →
      ∀ p : MvPolynomial (Fin n) ℂ,
        (∀ᶠ z in nhds (0 : V n), MvPolynomial.eval (fun k => f k z) p = 0) → p = 0 := by
  intro n f hf hdet p hp
  set F : V n → V n := fun z : V n => (WithLp.toLp 2 fun k => f k z : V n) with hF
  have hd : ∀ᶠ z in 𝓝 (0 : V n), DifferentiableAt ℂ F z := by
    filter_upwards [Filter.eventually_all.2 hf] with z hz
    exact differentiableAt_euclidean.2 hz
  have ha : AnalyticAt ℂ F 0 := GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hd
  have hs : HasStrictFDerivAt F
      (((fderiv ℂ F 0).toContinuousLinearEquivOfDetNeZero hdet : V n ≃L[ℂ] V n) :
        V n →L[ℂ] V n) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ha.hasStrictFDerivAt
  refine eq_zero_of_eventually_eval p (F 0) ?_
  rw [← hs.map_nhds_eq_of_equiv, Filter.eventually_map]
  exact hp

end GlobalTheory.JacobianIndependence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfDefinite
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.DefiniteFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma exists_diagonal_sgn_eq_smul_one (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    ∃ c : ℂ, c ≠ 0 ∧
      (Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = c • 1 := by
  rcases hp with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    ext a b
    by_cases hab : a = b <;> simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h, hab]
  · refine ⟨1, one_ne_zero, ?_⟩
    ext a b
    have ha : (a : ℕ) < X.p0 := lt_of_lt_of_le a.isLt h
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hab]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma norm_apply_le_sum_of_gram_eq_smul_one {n : ℕ} (G M M₀ : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : c ≠ 0) (h₀ : M₀.det ≠ 0)
    (hM₀ : M₀.transpose * G * M₀.map (starRingEnd ℂ) = c • 1)
    (hM : M.transpose * G * M.map (starRingEnd ℂ) = c • 1) (i j : Fin n) :
    ‖M i j‖ ≤ ∑ k, ‖M₀ i k‖ := by
  obtain ⟨V, rfl⟩ : ∃ V, M = M₀ * V :=
    ⟨M₀⁻¹ * M, (Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr h₀)).symm⟩
  have hVV : V.transpose * V.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.transpose_mul, Matrix.map_mul] at hM
    have h : V.transpose * (M₀.transpose * G * M₀.map (starRingEnd ℂ)) * V.map (starRingEnd ℂ)
        = c • 1 := by
      rw [← hM]; simp only [Matrix.mul_assoc]
    rw [hM₀, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h
    exact smul_right_injective _ hc h
  have hVV' : V.map (starRingEnd ℂ) * V.transpose = 1 := mul_eq_one_comm.mp hVV
  have hbound : ∀ a b, ‖V a b‖ ≤ 1 := by
    intro a b
    have h := congrFun (congrFun hVV' a) a
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at h
    have hs : ∑ k, Complex.normSq (V a k) = 1 := by
      have h' : ((∑ k, Complex.normSq (V a k) : ℝ) : ℂ) = 1 := by
        rw [← h]; push_cast; simp [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast h'
    have hle : Complex.normSq (V a b) ≤ 1 :=
      hs ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (V a k)) (Finset.mem_univ b)
    rw [Complex.normSq_eq_norm_sq] at hle
    nlinarith [norm_nonneg (V a b)]
  rw [Matrix.mul_apply]
  calc ‖∑ k, M₀ i k * V k j‖ ≤ ∑ k, ‖M₀ i k * V k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖M₀ i k‖ := Finset.sum_le_sum fun k _ => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hbound k j)


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.DefiniteFrames.isCompact_ortho (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    IsCompact {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} := by
  obtain ⟨c, hc, hD⟩ := exists_diagonal_sgn_eq_smul_one X hp
  rcases Set.eq_empty_or_nonempty {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} with he | ⟨x₀, hx₀⟩
  · rw [he]; exact isCompact_empty
  have hgram : ∀ {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}, X.IsOrtho x → ∀ τ : X.Ψ,
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).transpose * X.Gm.map (τ : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).map (starRingEnd ℂ)
        = c • 1 := by
    intro x hx τ
    rw [← _root_.PIW.FdPA.gram_eq, ← hD]
    exact hx τ
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ).det ≠ 0 := fun τ =>
    _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm _ (by rw [_root_.PIW.FdPA.gram_eq, hgram hx₀ τ]; simp [hc])
  have hU : ∀ τ : X.Ψ, Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := fun τ =>
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun τ => Set.univ.pi fun i =>
      Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) (∑ k, ‖x₀ τ i k‖))
    (isCompact_univ_pi fun τ => isCompact_univ_pi fun i => isCompact_univ_pi fun _ =>
      isCompact_closedBall _ _) ?_ ?_
  · simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    simp only [_root_.PIW.FdPA.gram_eq]
    exact ((hU τ).matrix_transpose.matrix_mul continuous_const).matrix_mul
      ((hU τ).matrix_map Complex.continuous_conj)
  · intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro τ i j
    exact norm_apply_le_sum_of_gram_eq_smul_one (X.Gm.map (τ : E →+* ℂ)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ) c hc (hdet τ) (hgram hx₀ τ) (hgram hx τ) i j

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma mem_dom_of_isOrtho' (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : X.IsOrtho x) :
    x ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho at hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  have hsgn : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := fun a => by
    rcases _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 a with h | h <;> simp [h]
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · apply _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm
    rw [hx τ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast hsgn a
  · have hmin : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
      rw [hx τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
      simp
    have hne : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
      exact Finset.prod_ne_zero_iff.mpr fun a _ => hsgn a
    rw [hmin, Complex.ofReal_re]
    exact mul_self_pos.mpr hne


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.DefiniteFrames.exists_compact_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ r ≤ X.p0) → ∃ C : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, ∃ γ ∈ X.Γ, ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ∈ C := by
  intro E _ _ _ r X hp
  refine ⟨{x | X.IsOrtho x}, _root_.GlobalTheory.DefiniteFrames.isCompact_ortho X hp,
    fun x hx => mem_dom_of_isOrtho' X hx,
    fun x hx => ⟨1, X.Γ.one_mem, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, ?_⟩⟩
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
    funext τ
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    rfl
  rw [h1]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx

end GlobalTheory.DefiniteFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FrameStepOfRightMulRealUnitaryGroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.UnitaryLift

open GlobalTheory.UnitaryFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma conj_unitary {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0)
    (c : X.Ψ → GL (Fin r) ℂ)
    (hc : ∀ τ, (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) :
    X.IsUnitaryC fun τ =>
      ((toGL X hx0 * c * (toGL X hx0)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) := by
    congr 1
    funext k
    unfold sgn
    split_ifs <;> simp
  have hy : IsOrth X
      (fun τ => (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
    intro τ
    have h0 := hx0 τ
    rw [gram_eq_mul, hJ] at h0
    change gram τ.1 X.Gm (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ)) = _
    rw [gram_eq_mul, hJ, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
          ((mat x0 τ)ᵀ * (X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ))) *
          (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h0, hc τ]
  have he : toGL X hy = toGL X hx0 * c := by
    funext τ
    exact Units.ext rfl
  rw [← he]
  exact quotient_unitary X hy hx0

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag {r p : ℕ} {a : Matrix (Fin r) (Fin r) ℂ}
    (ha : aᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) *
      a.map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1)) : a.det ≠ 0 := by
  have hD : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    split_ifs <;> norm_num
  intro h0
  have h := congrArg Matrix.det ha
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at h
  exact hD h.symm

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma conj_mul_inv_preserves_gram {r : ℕ} (G D M b : Matrix (Fin r) (Fin r) ℂ)
    (hM : IsUnit M.det) (hG : Mᵀ * (G * M.map (starRingEnd ℂ)) = D)
    (hb : bᵀ * D * b.map (starRingEnd ℂ) = D) :
    (M * b * M⁻¹)ᵀ * (G * (M * b * M⁻¹).map (starRingEnd ℂ)) = G := by
  obtain ⟨P, hP⟩ : ∃ P, P = M * b * M⁻¹ := ⟨_, rfl⟩
  rw [← hP]
  have hPM : P * M = M * b := by
    rw [hP, mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ hM, mul_one]
  have hT : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
  have hC : IsUnit (M.map (starRingEnd ℂ)).det := by
    have := (RingHom.map_det (starRingEnd ℂ) M).symm
    rw [show (starRingEnd ℂ).mapMatrix M = M.map (starRingEnd ℂ) from rfl] at this
    rw [this]
    exact hM.map _
  have key : Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ) =
      Mᵀ * G * M.map (starRingEnd ℂ) := by
    have e1 : Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ) =
        (P * M)ᵀ * G * (P * M).map (starRingEnd ℂ) := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [e1, hPM, Matrix.transpose_mul, Matrix.map_mul]
    calc bᵀ * Mᵀ * G * (M.map (starRingEnd ℂ) * b.map (starRingEnd ℂ))
        = bᵀ * (Mᵀ * (G * M.map (starRingEnd ℂ))) * b.map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = Mᵀ * G * M.map (starRingEnd ℂ) := by
          rw [hG, hb, ← hG, Matrix.mul_assoc]
  calc Pᵀ * (G * P.map (starRingEnd ℂ))
      = (Mᵀ)⁻¹ * (Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ))⁻¹ := by
        rw [← Matrix.mul_assoc (Mᵀ)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ hC, Matrix.nonsing_inv_mul_cancel_left _ _ hT]
    _ = (Mᵀ)⁻¹ * (Mᵀ * G * M.map (starRingEnd ℂ)) * (M.map (starRingEnd ℂ))⁻¹ := by rw [key]
    _ = G := by
        rw [← Matrix.mul_assoc (Mᵀ)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ hC, Matrix.nonsing_inv_mul_cancel_left _ _ hT]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UnitaryLift.step_of_right_mul :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  classical
  intro r X H hH x0 hx0 τ0 a s ha hs hsa
  have hM : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0).det :=
    isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx0 τ0)
  have ha' : IsUnit a.det := isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag ha)
  have hs' : IsUnit s.det := isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag hs)
  have horth : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)ᵀ * (X.Gm.map (τ0 : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0).map (starRingEnd ℂ)) =
      Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1 := by
    have h := hx0
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at h
    have h := h τ0
    rw [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul] at h
    rw [h]
    congr 1
    funext k
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  let ν : GL (Fin r) ℂ := Matrix.nonsingInvUnit _ hM
  have hmem : ∀ b : GL (Fin r) ℂ, (b : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) →
      (Pi.mulSingle τ0 (ν * b * ν⁻¹) : X.Ψ → GL (Fin r) ℂ) ∈ H := by
    intro b hb
    rw [hH]
    intro τ u w
    by_cases hτ : τ = τ0
    · beta_reduce
      rw [hτ, Pi.mulSingle_eq_same]
      have hcoe : ((ν * b * ν⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * b * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)⁻¹ := rfl
      rw [hcoe, _root_.GlobalTheory.UnitaryFrames.hermC_mulVec, _root_.GlobalTheory.UnitaryFrames.gram_eq_mul,
        conj_mul_inv_preserves_gram _ _ _ _ hM horth hb, _root_.GlobalTheory.UnitaryFrames.hermC_eq_dot]
    · beta_reduce
      rw [Pi.mulSingle_eq_of_ne hτ, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec]
  let αa : GL (Fin r) ℂ := Matrix.nonsingInvUnit a ha'
  let σ : GL (Fin r) ℂ := Matrix.nonsingInvUnit s hs'
  have hσ : σ * αa = αa⁻¹ * σ := Units.ext hsa
  have hσ' : σ * αa⁻¹ = αa * σ := by
    calc σ * αa⁻¹ = αa * (αa⁻¹ * σ) * αa⁻¹ := by group
      _ = αa * (σ * αa) * αa⁻¹ := by rw [hσ]
      _ = αa * σ := by group
  let hh : H := (⟨_, hmem αa ha⟩ : H)⁻¹
  have hh0 : ((hh : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * a⁻¹ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)⁻¹ := by
    simp only [hh, Subgroup.coe_inv, Pi.inv_apply, Pi.mulSingle_eq_same]
    rw [show (ν * αa * ν⁻¹)⁻¹ = ν * αa⁻¹ * ν⁻¹ by group]
    rfl
  have hhne : ∀ τ, τ ≠ τ0 → ((hh : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    intro τ hτ
    simp only [hh, Subgroup.coe_inv, Pi.inv_apply, Pi.mulSingle_eq_of_ne hτ, inv_one, Units.val_one]
  refine ⟨hh, ⟨_, hmem σ hs⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [hh, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul]
    congr 1
    calc ν * σ * ν⁻¹ * (ν * αa * ν⁻¹)⁻¹ = ν * (σ * αa⁻¹) * ν⁻¹ := by group
      _ = ν * (αa * σ) * ν⁻¹ := by rw [hσ']
      _ = ν * αa * ν⁻¹ * (ν * σ * ν⁻¹) := by group
  · intro g
    refine funext fun τ => ?_
    by_cases hτ : τ = τ0
    · rw [hτ]
      refine Eq.trans ?_ (@Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) τ0 _ _).symm
      change (((g * hh : H) : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 =
        ((g : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * a⁻¹
      rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hh0, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_right _ _ hM, Matrix.mul_assoc]
    · refine Eq.trans ?_ (@Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ hτ _ _).symm
      change (((g * hh : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ =
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
      rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hhne τ hτ, Matrix.mul_one]

end GlobalTheory.UnitaryLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.GamDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gamDisc : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X H _
  have hS := GlobalTheory.LatFin.latFin.2 r X 2
  set S := {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.GamDisc
end

