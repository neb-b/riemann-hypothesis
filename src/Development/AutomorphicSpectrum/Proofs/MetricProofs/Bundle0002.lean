module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsReversedTriangularFrameChange
section
open Matrix

namespace GlobalTheory.CompanionTheory.AdaptedFrame

variable {Φ : Type} [Field Φ] {r : ℕ}

def revMatrix (Φ : Type) [Field Φ] (r : ℕ) : Matrix (Fin r) (Fin r) Φ :=
  Matrix.of fun a b => if a = Fin.rev b then 1 else 0

theorem mul_revMatrix_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (A * revMatrix Φ r) a b = A a (Fin.rev b) := by
  simp [Matrix.mul_apply, revMatrix]

theorem revMatrix_mul_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (revMatrix Φ r * A) a b = A (Fin.rev a) b := by
  have : ∀ x : Fin r, (a = Fin.rev x) ↔ (x = Fin.rev a) := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, revMatrix, this]

theorem revMatrix_mul_self : revMatrix Φ r * revMatrix Φ r = 1 := by
  ext a b
  rw [mul_revMatrix_apply]
  simp [revMatrix, Matrix.one_apply, Fin.rev_rev]

theorem revMatrix_transpose : (revMatrix Φ r)ᵀ = revMatrix Φ r := by
  ext a b
  simp only [revMatrix, Matrix.transpose_apply, Matrix.of_apply]
  have : (b = Fin.rev a) ↔ (a = Fin.rev b) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

theorem inv_diag (U : Matrix (Fin r) (Fin r) Φ) (hU : U.BlockTriangular id)
    (hd : ∀ l, U l l ≠ 0) (l : Fin r) : U⁻¹ l l = (U l l)⁻¹ := by
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have h1 : (U * U⁻¹) l l = 1 := by
    rw [Matrix.mul_nonsing_inv U hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h1
  · exact eq_inv_of_mul_eq_one_right h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hU (show id k < id l from h)]; simp
    · rw [hinv (show id l < id k from h)]; simp
  · simp

theorem reversed_dual_frame :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ),
      IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) →
      (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 →
      (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm →
      ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧
        (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧
        R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  intro Φ _ R r u T U Rm Rm' hu hT hU hd hRm hRm' hmul h
  have hUdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hUinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have hutdet : IsUnit (uᵀ).det := by rwa [Matrix.det_transpose]
  have hTtdet : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  have hUtdet : IsUnit (Uᵀ).det := by rwa [Matrix.det_transpose]
  set P := revMatrix Φ r with hP
  have hPP : P * P = 1 := revMatrix_mul_self
  have hPt : Pᵀ = P := revMatrix_transpose
  have hrev : (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) = uᵀ⁻¹ * P := by
    ext a b
    rw [mul_revMatrix_apply]; rfl
  rw [hrev] at h

  have e1 : Tᵀ * (uᵀ⁻¹ * P * U * Rm') = 1 := by
    rw [h, Matrix.mul_assoc (Tᵀ⁻¹), hmul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hTtdet]
  have e2 : Rm'ᵀ * Uᵀ * P * u⁻¹ * T = 1 := by
    have := congrArg Matrix.transpose e1
    simp only [Matrix.transpose_mul, Matrix.transpose_one, hPt, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv] at this
    simpa [Matrix.mul_assoc] using this
  have e3 : T * (Rm'ᵀ * Uᵀ * P * u⁻¹) = 1 := mul_eq_one_comm.1 e2
  have e4 : T * Rm'ᵀ = u * P * Uᵀ⁻¹ := by
    have hk : (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹) = 1 := by
      calc (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)
          = Uᵀ * P * (u⁻¹ * u) * P * Uᵀ⁻¹ := by simp only [Matrix.mul_assoc]
        _ = Uᵀ * (P * P) * Uᵀ⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = 1 := by rw [hPP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hUtdet]
    calc T * Rm'ᵀ = T * Rm'ᵀ * ((Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)) := by rw [hk, Matrix.mul_one]
      _ = (T * (Rm'ᵀ * Uᵀ * P * u⁻¹)) * (u * P * Uᵀ⁻¹) := by simp only [Matrix.mul_assoc]
      _ = u * P * Uᵀ⁻¹ := by rw [e3, Matrix.one_mul]
  have hent : ∀ a b, (P * Uᵀ⁻¹ * P) a b = U⁻¹ (Fin.rev b) (Fin.rev a) := by
    intro a b
    rw [hP, mul_revMatrix_apply, revMatrix_mul_apply, ← Matrix.transpose_nonsing_inv,
      Matrix.transpose_apply]
  refine ⟨P * Uᵀ⁻¹ * P, Rm'ᵀ * P, P * Rmᵀ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    rw [hent]
    exact hUinv (show id (Fin.rev a) < id (Fin.rev b) from Fin.rev_lt_rev.2 hab')
  · intro l
    rw [hent]
    exact inv_diag U hU hd _
  · intro a b
    rw [mul_revMatrix_apply]; exact hRm' _ _
  · intro a b
    rw [revMatrix_mul_apply]; exact hRm _ _
  · calc Rm'ᵀ * P * (P * Rmᵀ) = Rm'ᵀ * (P * P) * Rmᵀ := by simp only [Matrix.mul_assoc]
      _ = (Rm * Rm')ᵀ := by rw [hPP, Matrix.mul_one, Matrix.transpose_mul]
      _ = 1 := by rw [hmul, Matrix.transpose_one]
  · calc u * (P * Uᵀ⁻¹ * P) = (u * P * Uᵀ⁻¹) * P := by simp only [Matrix.mul_assoc]
      _ = T * (Rm'ᵀ * P) := by rw [← e4, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.AdaptedFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ImLowerOnKernel
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ChartBlockLower

private theorem dotProduct_sum' {g a : ℕ} (v : Fin g → ℝ) (w : Fin a → Fin g → ℝ) :
    v ⬝ᵥ (∑ j, w j) = ∑ j, v ⬝ᵥ w j := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem quad_im_add_sum {a g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (s : Fin a → ℂ) (v : Fin g → ℝ) :
    v ⬝ᵥ (((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v)
      = v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)
        + ∑ j, (s j).im * (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
  have h : ((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im)
      = τ.map Complex.im + ∑ j, (s j).im • (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext i k
    simp [Matrix.sum_apply, Complex.im_sum]
  rw [h, Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum']
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem im_lower_on_kernel : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ v : Fin g → ℝ, (∀ j, z (Fin.castLE ha j) = 0 → (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v) := by
  intro n a g ha U τ0 B c hU hτ _ _ H z hz l hl _ v hv
  classical
  let l' : ℝ → Fin a → ℂ := fun t j => if z (Fin.castLE ha j) = 0 then -(t : ℂ) else l j
  let z' : ℝ → Fin n → ℂ := fun t i => if z i = 0 then Complex.exp (-(t : ℂ)) else z i
  have hT : Filter.Tendsto z' Filter.atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hzi : z i = 0
    · have h1 : Filter.Tendsto (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) Filter.atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      have h2 : (fun t : ℝ => z' t i) = fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) := by
        funext t
        simp [z', hzi, Complex.ofReal_exp]
      rw [h2, hzi]
      simpa using h1
    · have h2 : (fun t : ℝ => z' t i) = fun _ : ℝ => z i := by
        funext t
        simp [z', hzi]
      rw [h2]
      exact tendsto_const_nhds
  have hτc : ContinuousAt τ0 z := hτ.continuousAt (hU.mem_nhds hz)
  let φ : Matrix (Fin g) (Fin g) ℂ → ℝ := fun M => v ⬝ᵥ ((M.map Complex.im) *ᵥ v)
  have hφ : Continuous φ :=
    continuous_const.dotProduct
      ((continuous_id.matrix_map Complex.continuous_im).matrix_mulVec continuous_const)
  have hsplit : ∀ (w : Fin n → ℂ) (m : Fin a → ℂ),
      v ⬝ᵥ (((τ0 w + ∑ j, (m j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
          Complex.im) *ᵥ v)
        = φ (τ0 w) + ∑ j, (m j / (2 * Real.pi * Complex.I)).im *
            (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) :=
    fun w m => quad_im_add_sum (τ0 w) B (fun j => m j / (2 * Real.pi * Complex.I)) v
  have hsum : ∀ t : ℝ, ∑ j, (l' t j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))
      = ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    intro t
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hzj : z (Fin.castLE ha j) = 0
    · rw [hv j hzj]
      simp
    · simp [l', hzj]
  have hev : ∀ᶠ t in Filter.atTop, c * (v ⬝ᵥ v) ≤ φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    filter_upwards [hT.eventually_mem (hU.mem_nhds hz)] with t ht
    have hexp : ∀ j, Complex.exp (l' t j) = z' t (Fin.castLE ha j) := by
      intro j
      by_cases hzj : z (Fin.castLE ha j) = 0
      · simp [l', z', hzj]
      · simp [l', z', hzj, hl j hzj]
    have h0 := (H (z' t) ht (l' t) hexp).dotProduct_mulVec_nonneg v
    have hstar : star v = v := by
      funext i
      exact TrivialStar.star_trivial _
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hsplit, hsum] at h0
    linarith
  have hlim : Filter.Tendsto (fun t => φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))) Filter.atTop
      (𝓝 (φ (τ0 z) + ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)))) :=
    ((hφ.tendsto _).comp (hτc.tendsto.comp hT)).add tendsto_const_nhds
  rw [hsplit]
  exact ge_of_tendsto hlim hev

end GlobalTheory.CompanionTheory.ChartBlockLower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactSphere
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.GramCompact

private theorem exists_sum_norm_sq_eq_one_and_eq_sqrt_smul {m : Type} [Fintype m] (w : m → ℂ)
    (hw : 0 < ∑ k, ‖w k‖ ^ 2) :
    ∃ v : m → ℂ, ∑ k, ‖v k‖ ^ 2 = 1 ∧
      w = ((Real.sqrt (∑ k, ‖w k‖ ^ 2) : ℝ) : ℂ) • v := by
  have ht : 0 < Real.sqrt (∑ k, ‖w k‖ ^ 2) := Real.sqrt_pos.mpr hw
  have ht2 : Real.sqrt (∑ k, ‖w k‖ ^ 2) ^ 2 = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt hw.le
  refine ⟨(((Real.sqrt (∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · have h : ∀ k, ‖((((Real.sqrt (∑ j, ‖w j‖ ^ 2))⁻¹ : ℝ) : ℂ) • w) k‖ ^ 2 =
        (Real.sqrt (∑ j, ‖w j‖ ^ 2) ^ 2)⁻¹ * ‖w k‖ ^ 2 := by
      intro k
      rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    simp only [h]
    rw [← Finset.mul_sum, ht2, inv_mul_cancel₀ hw.ne']
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]

private theorem continuousOn_re_star_dotProduct_mulVec {X : Type} [TopologicalSpace X] {K : Set X}
    {m : Type} [Fintype m] {H : X → Matrix m m ℂ} (hH : ContinuousOn H K) (T : Set (m → ℂ)) :
    ContinuousOn (fun p : X × (m → ℂ) => (star p.2 ⬝ᵥ (H p.1 *ᵥ p.2)).re) (K ×ˢ T) := by
  have hd : Continuous (fun q : Matrix m m ℂ × (m → ℂ) => star q.2 ⬝ᵥ (q.1 *ᵥ q.2)) := by
    apply Continuous.dotProduct
    · exact continuous_snd.star
    · exact Continuous.matrix_mulVec continuous_fst continuous_snd
  have hfst : ContinuousOn (H ∘ Prod.fst) (K ×ˢ T) :=
    ContinuousOn.comp hH continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  have h2 : ContinuousOn (fun p : X × (m → ℂ) => ((H ∘ Prod.fst) p, p.2)) (K ×ˢ T) :=
    ContinuousOn.prodMk hfst continuousOn_snd
  have h3 := Continuous.comp_continuousOn (Continuous.comp Complex.continuous_re hd) h2
  exact h3

theorem isCompact_sphere (m : Type) [Fintype m] :
    IsCompact {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : m → ℂ)) (r := 1)).subset ?_
    intro w hw
    have hw' : ∑ k, ‖w k‖ ^ 2 = 1 := hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖w k‖ ^ 2 ≤ 1 := by
      calc ‖w k‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
              (Finset.mem_univ k)
        _ = 1 := hw'
    nlinarith [norm_nonneg (w k)]

theorem form_smul {m : Type} [Fintype m] (A : Matrix m m ℂ) (r : ℝ) (w : m → ℂ) :
    (star ((r : ℂ) • w) ⬝ᵥ (A *ᵥ ((r : ℂ) • w))).re = r ^ 2 * (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hs : star ((r : ℂ) • w) = (r : ℂ) • star w := by
    ext k
    simp
  rw [hs, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem exists_bounds (X : Type) [TopologicalSpace X] (K : Set X) (m : Type) [Fintype m]
    [DecidableEq m] (H : X → Matrix m m ℂ) (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ∀ w : m → ℂ,
      C⁻¹ * ∑ k, ‖w k‖ ^ 2 ≤ (star w ⬝ᵥ (H x *ᵥ w)).re ∧
        (star w ⬝ᵥ (H x *ᵥ w)).re ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : Set (m → ℂ), T = {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := ⟨_, rfl⟩
  have hKS : IsCompact (K ×ˢ T) := hT ▸ hK.prod (GlobalTheory.CompanionTheory.GramCompact.isCompact_sphere m)
  have hfc := continuousOn_re_star_dotProduct_mulVec hH T
  have hfpos : ∀ x ∈ K, ∀ w ∈ T, 0 < (star w ⬝ᵥ (H x *ᵥ w)).re := by
    intro x hx w hw
    rw [hT, Set.mem_setOf_eq] at hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    exact (Complex.pos_iff.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp (hpos x hx)).2 hw0)).1
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ w ∈ T,
      c ≤ (star w ⬝ᵥ (H x *ᵥ w)).re := by
    rcases (K ×ˢ T).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun x hx w hw => ?_⟩
      have hm : (x, w) ∈ K ×ˢ T := Set.mk_mem_prod hx hw
      rw [h] at hm
      exact absurd hm (Set.notMem_empty _)
    · obtain ⟨p₀, hp₀, hmin⟩ := hKS.exists_isMinOn h hfc
      refine ⟨_, hfpos p₀.1 (Set.mem_prod.mp hp₀).1 p₀.2 (Set.mem_prod.mp hp₀).2,
        fun x hx w hw => ?_⟩
      exact hmin (Set.mk_mem_prod hx hw)
  obtain ⟨M, hM⟩ := hKS.exists_bound_of_continuousOn hfc
  have hC1 : c⁻¹ ≤ max 1 (max c⁻¹ M) := (le_max_left _ _).trans (le_max_right _ _)
  have hCM : M ≤ max 1 (max c⁻¹ M) := (le_max_right _ _).trans (le_max_right _ _)
  have hCc : (max 1 (max c⁻¹ M))⁻¹ ≤ c := inv_le_of_inv_le₀ hc0 hC1
  refine ⟨max 1 (max c⁻¹ M), le_max_left _ _, ?_⟩
  intro x hx w
  have hs0 : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun k _ => by positivity)
  rcases hs0.eq_or_lt with hs | hspos
  · have hw : w = 0 := by
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hs.symm k
        (Finset.mem_univ k)
      simpa using this
    subst hw
    simp
  · obtain ⟨v, hv1, hwv⟩ := exists_sum_norm_sq_eq_one_and_eq_sqrt_smul w hspos
    have hvT : v ∈ T := by
      rw [hT]
      exact hv1
    have hq : (star w ⬝ᵥ (H x *ᵥ w)).re =
        (∑ k, ‖w k‖ ^ 2) * (star v ⬝ᵥ (H x *ᵥ v)).re := by
      conv_lhs => rw [hwv]
      rw [GlobalTheory.CompanionTheory.GramCompact.form_smul, Real.sq_sqrt hs0]
    have h1 : c ≤ (star v ⬝ᵥ (H x *ᵥ v)).re := hc x hx v hvT
    have h2 : (star v ⬝ᵥ (H x *ᵥ v)).re ≤ M := by
      have h3 : ‖(star v ⬝ᵥ (H x *ᵥ v)).re‖ ≤ M := hM (x, v) (Set.mk_mem_prod hx hvT)
      rw [Real.norm_eq_abs] at h3
      exact (le_abs_self _).trans h3
    rw [hq]
    have h4 := mul_le_mul_of_nonneg_right hCc hspos.le
    have h5 := mul_le_mul_of_nonneg_right h1 hspos.le
    have h6 := mul_le_mul_of_nonneg_right (h2.trans hCM) hspos.le
    constructor
    · linarith
    · linarith

end GlobalTheory.CompanionTheory.GramCompact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
section
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

noncomputable def iter {B V : Type} (h : B × V → V) : ℕ → B × V → V
  | 0, p => p.2
  | k + 1, p => h (p.1, iter h k p)

@[simp] theorem iter_zero {B V : Type} (h : B × V → V) (p : B × V) : iter h 0 p = p.2 := rfl

theorem iter_succ {B V : Type} (h : B × V → V) (k : ℕ) (p : B × V) :
    iter h (k + 1) p = h (p.1, iter h k p) := rfl

section Norms

variable {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]

theorem norm_iter_le (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ := by
  have key : ∀ k : ℕ, ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ ∧ iter h k (b, s) ∈ ball (0 : V) ρ := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      simpa using hs
    | succ k ih =>
      have hk := hcontr b hb _ ih.2
      have e : iter h (k + 1) (b, s) = h (b, iter h k (b, s)) := rfl
      rw [e]
      refine ⟨?_, ?_⟩
      · calc ‖h (b, iter h k (b, s))‖ ≤ 3 / 5 * ‖iter h k (b, s)‖ := hk
          _ ≤ 3 / 5 * ((3 / 5) ^ k * ‖s‖) := by gcongr; exact ih.1
          _ = (3 / 5) ^ (k + 1) * ‖s‖ := by ring
      · have h2 := mem_ball_zero_iff.mp ih.2
        rw [mem_ball_zero_iff]
        nlinarith [norm_nonneg (iter h k (b, s))]
  exact (key k).1

theorem iter_mem_ball (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    iter h k (b, s) ∈ ball (0 : V) ρ := by
  rw [mem_ball_zero_iff]
  have h1 := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : (3 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : ‖s‖ < ρ := mem_ball_zero_iff.mp hs
  nlinarith [norm_nonneg s]

end Norms

theorem iter_differentiableOn {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hd : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : V) ρ))
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) (k : ℕ) :
    DifferentiableOn ℂ (iter h k) (ball b₀ ρ ×ˢ ball (0 : V) ρ) := by
  induction k with
  | zero =>
    have e : iter h 0 = Prod.snd := funext fun p => rfl
    rw [e]
    exact differentiableOn_snd
  | succ k ih =>
    have e : iter h (k + 1) = h ∘ fun p => (p.1, iter h k p) := funext fun p => rfl
    rw [e]
    refine hd.comp (differentiableOn_fst.prodMk ih) ?_
    intro p hp
    exact Set.mk_mem_prod hp.1 (iter_mem_ball b₀ h ρ hcontr hp.1 hp.2 k)

theorem medial_eventually {B V : Type} [TopologicalSpace B] [Zero V] [TopologicalSpace V] (b₀ : B)
    (μ : B × V × V → V) (hc : ContinuousAt μ (b₀, 0, 0)) (h0 : μ (b₀, 0, 0) = 0)
    (hcomm : ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1))
    (hassoc : ∀ᶠ p : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) :
    ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.1), μ (p.1, p.2.2, p.2.2)) = μ (p.1, μ p, μ p) := by
  have hfst : Tendsto (fun p : B × V × V => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) := continuous_fst.tendsto _
  have hs : Tendsto (fun p : B × V × V => p.2.1) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_fst.comp continuous_snd).tendsto _
  have ht : Tendsto (fun p : B × V × V => p.2.2) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_snd.comp continuous_snd).tendsto _
  have hμ : Tendsto μ (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    have := hc.tendsto
    rwa [h0] at this
  have htt : Tendsto (fun p : B × V × V => μ (p.1, p.2.2, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    hμ.comp (hfst.prodMk_nhds (ht.prodMk_nhds ht))
  have orbitMap_conj_smul_one := (hfst.prodMk_nhds (hs.prodMk_nhds (hs.prodMk_nhds htt))).eventually hassoc
  have orbitMap_conj_smul_two := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds ht))).eventually hassoc
  have selfLieBasisVector := (hfst.prodMk_nhds (ht.prodMk_nhds (hs.prodMk_nhds ht))).eventually hassoc
  have eA4 := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds hμ))).eventually hassoc
  filter_upwards [orbitMap_conj_smul_one, orbitMap_conj_smul_two, selfLieBasisVector, eA4, hcomm] with ⟨b, s, t⟩ a1 a2 a3 a4 c
  dsimp only at a1 a2 a3 a4 c ⊢
  calc μ (b, μ (b, s, s), μ (b, t, t)) = μ (b, s, μ (b, s, μ (b, t, t))) := a1
    _ = μ (b, s, μ (b, μ (b, s, t), t)) := by rw [a2]
    _ = μ (b, s, μ (b, μ (b, t, s), t)) := by rw [c]
    _ = μ (b, s, μ (b, t, μ (b, s, t))) := by rw [a3]
    _ = μ (b, μ (b, s, t), μ (b, s, t)) := a4.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

