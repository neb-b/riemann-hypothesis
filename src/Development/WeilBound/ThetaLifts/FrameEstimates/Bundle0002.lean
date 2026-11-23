module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace SignatureOfHermitianForm

theorem sig_sq {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : r + s = n) (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ)
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    M.det ≠ 0 ∧ Function.Surjective A.mulVec := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr h.symm).trans finSumFinEquiv.symm
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e
  have h1 : A'ᵀ * M * A'.map star
      = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e e := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have h2 : A'.det * M.det * (A'.map star).det ≠ 0 := by
    rw [← Matrix.det_transpose A', ← Matrix.det_mul, ← Matrix.det_mul, h1, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  have h3 : A'.det ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h2)
  refine ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h2), fun x => ?_⟩
  have hu : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').2 (Ne.isUnit h3)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu x
  refine ⟨u ∘ e.symm, ?_⟩
  rw [← hu]
  ext i
  simp only [A', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp]
  rw [← e.sum_comp]
  simp

theorem block_form {r s : ℕ} (w : Fin r ⊕ Fin s → ℂ) :
    w ⬝ᵥ (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) *ᵥ star w
      = ((∑ i, Complex.normSq (w (Sum.inl i)) - ∑ j, Complex.normSq (w (Sum.inr j)) : ℝ) : ℂ) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem sig_index {n r s k : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (c : ℂ) (hc : c ≠ 0)
    (x y : Fin k → Fin n → ℂ) (hxx : ∀ i j, x i ⬝ᵥ M *ᵥ star (x j) = 0)
    (hxy : ∀ i j, x i ⬝ᵥ M *ᵥ star (y j) = if i = j then c else 0) : k ≤ min r s := by
  obtain ⟨h, A, hA⟩ := h
  choose u hu using fun i => (sig_sq h A hA).2 (x i)
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin r ⊕ Fin s → ℂ) := Fintype.linearCombination ℂ u
  have hL : ∀ v, A *ᵥ L v = ∑ i, v i • x i := by
    intro v
    simp only [L, Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hu]
  have hinj : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    have h0 := hL v
    rw [hv, Matrix.mulVec_zero] at h0
    ext j
    have h1 := congrArg (fun z => z ⬝ᵥ M *ᵥ star (y j)) h0
    simp only [zero_dotProduct, sum_dotProduct, smul_dotProduct, hxy, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right hc
  have hiso : ∀ v, ∑ i, Complex.normSq (L v (Sum.inl i)) = ∑ j, Complex.normSq (L v (Sum.inr j)) := by
    intro v
    have h1 := block_form (L v)
    have h2 : (A *ᵥ L v) ⬝ᵥ M *ᵥ star (A *ᵥ L v) = 0 := by
      rw [hL]
      simp only [star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, smul_dotProduct,
        dotProduct_sum, dotProduct_smul, hxx, smul_zero, Finset.sum_const_zero]
    have h3 : star (A *ᵥ L v) = A.map star *ᵥ star (L v) := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    rw [h3, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hA, h1] at h2
    exact sub_eq_zero.1 (Complex.ofReal_eq_zero.1 h2)
  have hz : ∀ {m : ℕ} (f : Fin m → ℂ), ∑ i, Complex.normSq (f i) = 0 → ∀ i, f i = 0 := by
    intro m f hf i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (f i)).1 hf i (Finset.mem_univ i))
  refine le_min ?_ ?_
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inl) ∘ₗ L) (by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inl i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inr j)) (by rw [← hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h1 i
      · exact h2 j)
    simpa using this
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ L) (by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inr i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inl j)) (by rw [hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h2 i
      · exact h1 j)
    simpa using this

theorem form_map {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (x y : Fin n → E) :
    (fun i => τ (x i)) ⬝ᵥ (c • J.map τ) *ᵥ star (fun i => τ (y i)) = c * τ (x ⬝ᵥ J *ᵥ fun i => σ (y i)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, Matrix.mulVec, hτ]

theorem of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x)) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : HasSig (c • J.map τ) r s) :
    J.det ≠ 0 ∧ r + s = n ∧ ∀ fr : Frame σ J, fr.IsGood → fr.r ≤ min r s := by
  refine ⟨?_, h.1, fun fr hfr => ?_⟩
  · obtain ⟨h, A, hA⟩ := h
    intro h0
    apply (sig_sq h A hA).1
    have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [Matrix.det_smul, this, h0, map_zero, mul_zero]
  · refine sig_index h c hc (fun i l => τ (fr.x i l)) (fun i l => τ (fr.y i l)) (fun i j => ?_) (fun i j => ?_)
    · have := hfr.xx i j
      unfold form at this
      rw [form_map σ τ hτ, this, map_zero, mul_zero]
    · have := hfr.xy i j
      unfold form at this
      rw [form_map σ τ hτ, this]
      split_ifs <;> simp

end SignatureOfHermitianForm

theorem epsOf_of : EpsOf := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩

end PositivityTheory.ThKEst
end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
section
namespace PositivityTheory.ThKEst

theorem coefReal_of : CoefReal := fun _ _ _ _ _ _ N => RealFourierCoefficientBounds.main N

end PositivityTheory.ThKEst
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.FinBound
section
open MeasureTheory Filter Topology GlobalTheory.WeilM

noncomputable section
namespace PositivityTheory.ThKEst.W

theorem real_bound (h : CoefReal) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] (β : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hβ : ∀ y, β y = 0 → y = 0) :
    ∃ ν : Measure Y, ν.IsAddHaarMeasure ∧ ∀ N : ℕ, ∃ p : Seminorm ℂ (SchwartzMap Y ℂ), Continuous p ∧
      ∀ (f₁ f₂ : SchwartzMap Y ℂ) (x y : Y), ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) *
        (starRingEnd ℂ) (f₂ u) ∂ν‖ * (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ Y))
  let T : V ≃L[ℝ] Y := (toEuclidean (E := Y)).symm
  refine ⟨Measure.map T volume, T.isAddHaarMeasure_map _, fun N => ?_⟩
  obtain ⟨p, hp, hb⟩ := h V N
  let S : Y →ₗ[ℝ] (V →L[ℝ] ℝ) := (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ
    (β.compl₂ T.toLinearEquiv.toLinearMap)
  have hS : ∀ y v, S y v = β y (T v) := fun _ _ => rfl
  obtain ⟨K₁, -, hK₁⟩ := S.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 fun y hy => hβ y (LinearMap.ext fun u => by
    have := hS y (T.symm u)
    rw [hy, T.apply_symm_apply] at this
    exact this.symm))
  let K : NNReal := 1 + K₁ + ‖(T : V →L[ℝ] Y)‖₊
  have hK : (K : ℝ) = 1 + K₁ + ‖(T : V →L[ℝ] Y)‖ := rfl
  let c := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  refine ⟨K ^ N • p.comp c.toLinearMap, (hp.comp c.continuous).const_smul (K ^ N), fun f₁ f₂ x y => ?_⟩
  have h1 := hb (c f₁) (c f₂) (T.symm x) ((InnerProductSpace.toDual ℝ V).symm (S y))
  have e : ∫ u, Complex.exp (2 * Real.pi * Complex.I * (β y u : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)
      ∂(Measure.map T volume) = ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ u ((InnerProductSpace.toDual ℝ V).symm (S y)) : ℝ)) * c f₁ (u + T.symm x) * (starRingEnd ℂ) (c f₂ u) := by
    rw [show Measure.map T volume = Measure.map T.toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [real_inner_comm _ u, InnerProductSpace.toDual_symm_apply, hS]
    simp [c]
  rw [e]
  rw [LinearIsometryEquiv.norm_map] at h1
  have hx : ‖x‖ ≤ ‖(T : V →L[ℝ] Y)‖ * ‖T.symm x‖ := by simpa using (T : V →L[ℝ] Y).le_opNorm (T.symm x)
  have hy : ‖y‖ ≤ K₁ * ‖S y‖ := by
    have := hK₁.le_mul_dist y 0
    rwa [map_zero, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at this
  have n1 := norm_nonneg (T : V →L[ℝ] Y)
  have n2 := norm_nonneg (T.symm x)
  have n3 := norm_nonneg (S y)
  have n4 := K₁.coe_nonneg
  have h2 : 1 + ‖x‖ + ‖y‖ ≤ K * (1 + ‖T.symm x‖ + ‖S y‖) := by
    rw [hK]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n4 n2]
  have hK1 : (1 : ℝ) ≤ K ^ N := one_le_pow₀ (by rw [hK]; linarith)
  have q := mul_nonneg (apply_nonneg p (c f₁)) (apply_nonneg p (c f₂))
  calc _ ≤ _ * (K * (1 + ‖T.symm x‖ + ‖S y‖)) ^ N := by gcongr
    _ = K ^ N * (_ * (1 + ‖T.symm x‖ + ‖S y‖) ^ N) := by rw [mul_pow, mul_left_comm]
    _ ≤ K ^ N * (p (c f₁) * p (c f₂)) := by gcongr
    _ ≤ K ^ N * (K ^ N * (p (c f₁) * p (c f₂))) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left q hK1) (zero_le_one.trans hK1)
    _ = _ := by
      simp only [Seminorm.smul_apply, Seminorm.comp_apply, NNReal.smul_def, NNReal.coe_pow, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
      ring

theorem sb_inv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {φ : G → ℂ} (hφ : φ ∈ SB G) :
    ∀ᶠ k in 𝓝 (0 : G), ∀ x, φ (x + k) = φ x := by
  have h1 : ∀ᶠ k in 𝓝 (0 : G), ∀ x ∈ tsupport φ, φ (x + k) = φ x ∧ φ (x - k) = φ x :=
    hφ.2.isCompact.eventually_forall_of_forall_eventually fun x _ => by
      have a := (hφ.1.comp_continuous (f := fun z : G × G => z.2 + z.1) (by fun_prop)).eventually_eq (0, x)
      have b := (hφ.1.comp_continuous (f := fun z : G × G => z.2 - z.1) (by fun_prop)).eventually_eq (0, x)
      have c := (hφ.1.comp_continuous (f := fun z : G × G => z.2) (by fun_prop)).eventually_eq (0, x)
      filter_upwards [a, b, c] with z a b c
      simp only [Function.comp, add_zero, sub_zero] at a b c
      exact ⟨a.trans c.symm, b.trans c.symm⟩
  filter_upwards [h1] with k hk x
  by_cases hx : x ∈ tsupport φ
  · exact (hk x hx).1
  by_cases hx' : x + k ∈ tsupport φ
  · simpa using (hk _ hx').2.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem fin_bound {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] (ν : Measure G) [ν.IsAddHaarMeasure] (χ : H → G → ℂ) (hn : ∀ y u, ‖χ y u‖ = 1)
    (ha : ∀ y u u', χ y (u + u') = χ y u * χ y u')
    (hd : ∀ U ∈ 𝓝 (0 : G), ∃ K, IsCompact K ∧ ∀ y, (∀ u ∈ U, χ y u = 1) → y ∈ K) {φ₁ φ₂ : G → ℂ} (h₁ : φ₁ ∈ SB G)
    (h₂ : φ₂ ∈ SB G) : ∃ (C : ℝ) (K : Set (G × H)), IsCompact K ∧ ∀ x y,
      ‖∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν‖ ≤ C ∧
      (∫ u, χ y u * φ₁ (u + x) * (starRingEnd ℂ) (φ₂ u) ∂ν ≠ 0 → (x, y) ∈ K) := by
  obtain ⟨C, hC⟩ := h₁.1.continuous.bounded_above_of_compact_support h₁.2
  obtain ⟨K, hK, hK'⟩ := hd _ ((sb_inv h₁).and (sb_inv h₂))
  have hi : Integrable φ₂ ν := h₂.1.continuous.integrable_of_hasCompactSupport h₂.2
  refine ⟨∫ u, C * ‖φ₂ u‖ ∂ν, ((fun z : G × G => z.1 - z.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) ×ˢ K,
    ((h₁.2.isCompact.prod h₂.2.isCompact).image (by fun_prop)).prod hK, fun x y => ⟨?_, fun h0 => ⟨?_, hK' y fun k hk => ?_⟩⟩⟩
  · refine norm_integral_le_of_norm_le (hi.norm.const_mul C) (.of_forall fun u => ?_)
    rw [norm_mul, norm_mul, hn, one_mul, RCLike.norm_conj]
    gcongr
    exact hC _
  · by_contra hx
    refine h0 (integral_eq_zero_of_ae (.of_forall fun u => ?_))
    by_contra hu
    simp only [Pi.zero_apply, mul_eq_zero, not_or, map_eq_zero] at hu
    exact hx ⟨(u + x, u), ⟨subset_tsupport _ hu.1.2, subset_tsupport _ hu.2⟩, add_sub_cancel_left _ _⟩
  · refine (mul_eq_right₀ h0).1 ?_
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ k]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only
    rw [ha, add_right_comm, hk.1, hk.2]
    ring

end PositivityTheory.ThKEst.W
end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.FrameBasis
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cm_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem rId_zero : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

def formL (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := form σ J x y
  map_add' a b := by simp [form, add_dotProduct]
  map_smul' c a := by simp [form, smul_dotProduct]

omit [NumberField F] [NumberField E] in
theorem formL_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) : formL σ J y x = form σ J x y := rfl

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ ε : E, ε * ε = 1 ∧ ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
  have key : ∀ ε : E, (∀ i j, σ (J j i) = ε * J i j) → ε * ε = 1 → ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
    intro ε h1 h2 x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_invol h, h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(y j * J j i * σ (x i))) * h2
  rcases hJ.1 with h1 | h1
  · exact ⟨1, by simp, key 1 (by simpa using h1) (by simp)⟩
  · exact ⟨-1, by simp, key (-1) (by simpa using h1) (by simp)⟩

theorem frameBasis_of : FrameBasis := by
  intro F E _ _ _ _ _ σ hσ n J hJ fr hfr
  classical
  obtain ⟨ε, hε, hsw⟩ := form_swap hσ hJ
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have yx : ∀ i j, form σ J (fr.y i) (fr.x j) = if i = j then ε else 0 := by
    intro i j
    rw [hsw, hfr.xy]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  let K : Submodule E (Fin n → E) := ⨅ i, (LinearMap.ker (formL σ J (fr.x i)) ⊓ LinearMap.ker (formL σ J (fr.y i)))
  have hK : ∀ u, u ∈ K ↔ ∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0 := by
    intro u
    simp [K, Submodule.mem_iInf, formL_apply]
  let bK := Module.finBasis E K
  let v : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → Fin n → E :=
    Sum.elim (Sum.elim fr.x fr.y) fun k => (bK k : Fin n → E)
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ j, g (.inl (.inl j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.y j)) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xy, hfr.yy, ((hK _).1 (bK _).2 j).2] using this
    have h2 : ∀ j, g (.inl (.inr j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.x j)) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xx, yx, ((hK _).1 (bK _).2 j).1, hε0] using this
    have h3 : ∑ k, g (.inr k) • bK k = 0 := by
      apply Subtype.ext
      simpa [Fintype.sum_sum_type, v, h1, h2] using hg
    have h4 := Fintype.linearIndependent_iff.1 bK.linearIndependent _ h3
    rintro ((j | j) | j)
    exacts [h1 j, h2 j, h4 j]
  have hsp : ⊤ ≤ Submodule.span E (Set.range v) := by
    intro u _
    let a := ∑ i, form σ J u (fr.y i) • fr.x i + ∑ i, (ε * form σ J u (fr.x i)) • fr.y i
    have ha : a ∈ Submodule.span E (Set.range v) :=
      add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inl i), rfl⟩))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inr i), rfl⟩))
    have hu : u - a ∈ K := by
      rw [hK]
      intro j
      constructor
      · rw [← formL_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [a, map_sub, map_add (f := _), map_sum, map_smul, formL_apply, hfr.xx, yx, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination (-form σ J u (fr.x j)) * hε
      · rw [← formL_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [a, map_sub, map_add (f := _), map_sum, map_smul]
        simp [formL_apply, hfr.xy, hfr.yy]
    have hb : u - a ∈ Submodule.span E (Set.range v) := by
      have : u - a = ∑ k, bK.repr ⟨_, hu⟩ k • (bK k : Fin n → E) := by
        have := congrArg Subtype.val (bK.sum_repr ⟨_, hu⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr i, rfl⟩)
    simpa using add_mem hb ha
  let B := Module.Basis.mk hli hsp
  let e : ((Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K)) ≃ Fin n := B.indexEquiv (Pi.basisFun E (Fin n))
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun l k => v (e.symm k) l
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  let lam0 : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ :=
    Sum.elim (Sum.elim (fun i => LinearMap.proj i) fun i => -LinearMap.proj i) fun _ => 0
  refine ⟨hM.unit, fun k => lam0 (e.symm k), ⟨fun i => e (.inl (.inl i)), fun i j h => by simpa using h⟩,
    ⟨fun i => e (.inl (.inr i)), fun i j h => by simpa using h⟩, fun i j h => by simpa using e.injective h,
    fun i t => ⟨congrArg (fun z => lam0 z t) (e.symm_apply_apply _), congrArg (fun z => lam0 z t) (e.symm_apply_apply _)⟩,
    fun k hk => ?_, fun i => congrArg v (e.symm_apply_apply _), fun t => ?_⟩
  · obtain ⟨k, rfl⟩ := e.surjective k
    rcases k with (j | j) | j
    · exact absurd rfl (hk j).1
    · exact absurd rfl (hk j).2
    · simp [lam0]
  · have key : ∀ k, mat (fr.a t) *ᵥ incV F (v k) = rId F (lam0 k t) • incV F (v k) := by
      rintro ((j | j) | j)
      · exact hfr.ax t j
      · exact hfr.ay t j
      · have := hfr.a0 t _ ((hK _).1 (bK j).2)
        simpa [lam0, rId_zero, v] using this
    ext l k
    have := congrFun (key (e.symm k)) l
    rw [Matrix.mul_diagonal, mul_comm, ← Algebra.smul_def]
    exact this

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DomU {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)) : Prop :=
  ∃ k : ℕ, ∀ φ ∈ 𝓕, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (G : UA σ X.J → ℝ≥0∞), Continuous p ∧ Measurable G ∧
    ∫⁻ g in M.dom, G g ∂M.μ < ⊤ ∧ ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * G g

def DomWeilU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (d + 2 * min r s < 2 * n ∨ min r s = 0) → DomU M om {φ | φ ∈ SB _}

def SoSemiU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ N : ℕ, ∃ k : ℕ, ∀ φ ∈ soFin B M, ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
    ∀ (f : SInf F (Fin n × Fin d)) g h, ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ p f * (ht h : ℝ) ^ k

def DomSoU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → DomU M om (soFin B M)

theorem domWeil_of_U (h : DomWeilU) : DomWeil := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hd φ hφ
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP hd
  obtain ⟨p, G, hp, hG, hint, hb⟩ := hk φ hφ
  exact ⟨p, k, G, hp, hG, hint, hb⟩

theorem soSemi_of_U (h : SoSemiU) : SoSemi := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ N
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP N
  obtain ⟨p, hp, hb⟩ := hk φ hφ
  exact ⟨p, k, hp, hb⟩

end PositivityTheory.ThKEst

end
end

