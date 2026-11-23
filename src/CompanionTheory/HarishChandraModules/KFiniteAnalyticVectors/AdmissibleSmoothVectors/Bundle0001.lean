module

public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingAvg
section
open MeasureTheory Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted.Gard

section Param

variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_iter_partial (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1 := by
  have h : (fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1) =
      fun p => (iteratedFDeriv ℝ k Φ p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
    funext p
    have e : (fun y => Φ (y, p.2)) =
        (fun z => Φ (z + (0, p.2))) ∘ (ContinuousLinearMap.inl ℝ P Q) := by
      funext y; simp
    have hs : ContDiff ℝ ∞ (fun z : P × Q => Φ (z + (0, p.2))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp
  rw [h]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

end Param

section Avg

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_w (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : G → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) (u : H) : Integrable (fun x => w x • ρ x u) μ :=
  (hw.smul (hρ u)).integrable_of_hasCompactSupport hc.smul_right

theorem exists_strictHenselian_absolutely_closed_local_ring (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (hiso : ∀ x u, ‖ρ x u‖ = ‖u‖)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  refine ⟨L.mkContinuous (∫ x, ‖w x‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

theorem integral_mul_right_of_conj {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w)
    (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (F : G → H) :
    ∫ x, F (x * k) ∂μ = ∫ x, F x ∂μ := by
  have hm := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have hemb : MeasurableEmbedding fun x : G => x * k := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have e1 : ∫ x, w (x * k) ∂μ = ∫ x, w x ∂μ := by
    rw [← integral_mul_left_eq_self (fun x => w (x * k)) k⁻¹]
    simp only [hk]
  rw [← hemb.integral_map, hm, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at e1
  have e2 : Measure.modularCharacterFun k = 1 := by
    have : ((Measure.modularCharacterFun k : NNReal) : ℝ) = 1 := by
      apply mul_right_cancel₀ hpos.ne'
      rw [e1, one_mul]
    exact_mod_cast this
  rw [← hemb.integral_map, hm, e2, one_smul]

theorem apply_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (g : G) (u : H) :
    ρ g (∫ x, w x • ρ x u ∂μ) = ∫ x, w (g⁻¹ * x) • ρ x u ∂μ := by
  rw [← (ρ g).integral_comp_comm (integrable_w μ ρ hρ hw hc u),
    ← integral_mul_left_eq_self (fun x => w (g⁻¹ * x) • ρ x u) g]
  congr 1
  funext x
  rw [inv_mul_cancel_left, hmul, ContinuousLinearMap.map_smul_of_tower]

theorem T_comm (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (h0 : 0 ≤ w) (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (u : H) :
    ∫ x, w x • ρ x (ρ k u) ∂μ = ρ k (∫ x, w x • ρ x u ∂μ) := by
  rw [apply_alt μ ρ hρ hmul hw hc,
    ← integral_mul_right_of_conj μ hw hc h0 h1 k hk (fun x => w (k⁻¹ * x) • ρ x u)]
  congr 1
  funext x
  rw [← mul_assoc, hk, hmul]

theorem exists_nhds_close (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (h1 : ∀ u, ρ 1 u = u)
    (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, ∀ y ∈ Y, ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖ := by
  let A : G → (Y →L[ℂ] H) := fun x => (ρ x).comp Y.subtypeL - Y.subtypeL
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro y
    exact (hρ y).sub continuous_const
  have hA1 : A 1 = 0 := by
    ext y
    simp [A, h1]
  refine ⟨{x | ‖A x‖ < 1 / 2}, ?_, fun x hx y hy => ?_⟩
  · exact (isOpen_lt hA.norm continuous_const).mem_nhds (by simp [hA1])
  · have := (A x).le_opNorm ⟨y, hy⟩
    exact this.trans (mul_le_mul_of_nonneg_right (le_of_lt hx) (norm_nonneg _))

theorem eq_zero_of_alt_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w) (h1 : w 1 ≠ 0)
    (y : H) (hy : ∀ x, w x ≠ 0 → ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖) (hT : ∫ x, w x • ρ x y ∂μ = 0) : y = 0 := by
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport hc
  have e : ∫ x, w x • (ρ x y - y) ∂μ = -((∫ x, w x ∂μ) • y) := by
    simp only [smul_sub]
    rw [integral_sub (integrable_w μ ρ hρ hw hc y) (hwi.smul_const y), hT, integral_smul_const, zero_sub]
  have b : ‖∫ x, w x • (ρ x y - y) ∂μ‖ ≤ ∫ x, w x * (1 / 2 * ‖y‖) ∂μ := by
    refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_of_nonneg (h0 x)]
    by_cases hx : w x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left (hy x hx) (h0 x)
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at b
  have := le_of_mul_le_mul_left b hpos
  have h2 : ‖y‖ = 0 := by linarith [norm_nonneg y]
  exact norm_eq_zero.1 h2

end Avg

theorem exists_preimage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (Y : Submodule ℂ H)
    [FiniteDimensional ℂ Y] (T : H →L[ℂ] H) (hT : ∀ y ∈ Y, T y ∈ Y) (hi : ∀ y ∈ Y, T y = 0 → y = 0) :
    ∀ v ∈ Y, ∃ u, T u = v := by
  intro v hv
  let L : Y →ₗ[ℂ] Y := (T : H →ₗ[ℂ] H).restrict hT
  have hL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hi y y.2 (congrArg Subtype.val hy))
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hL ⟨v, hv⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end CompanionTheory.D.gk.admitted.Gard
end
end

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaChol
section
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

theorem isUpperTriangular_conjTranspose_iff {A : Matrix n n 𝕜} :
    Aᴴ.IsUpperTriangular ↔ A.IsLowerTriangular := by
  constructor
  · intro h i j hij
    have := h (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij)
    simpa [conjTranspose_apply] using this
  · intro h i j hij
    have := h (show OrderDual.toDual i < OrderDual.toDual j from hij)
    simp [conjTranspose_apply, this]

section Existence

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_isUpperTriangular_conjTranspose_mul_self {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ Rᴴ * R = S := by
  have hL : (LDL.lower hS).IsLowerTriangular := LDL.isLowerTriangular_lower hS
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 (isUnit_of_invertible (LDL.lowerInv hS)))
  have hpos : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  set d : n → ℝ := fun i => RCLike.re (LDL.diagEntries hS i)
  have hd : ∀ i, LDL.diagEntries hS i = (d i : 𝕜) := fun i => by
    obtain ⟨_, him⟩ := RCLike.pos_iff.1 (hpos i)
    rw [← RCLike.re_add_im (LDL.diagEntries hS i), him]; simp [d]
  have hd0 : ∀ i, 0 ≤ d i := fun i => (RCLike.pos_iff.1 (hpos i)).1.le
  refine ⟨diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ,
    (blockTriangular_diagonal _).mul (isUpperTriangular_conjTranspose_iff.2 hL), ?_⟩
  have hsq : (diagonal (fun i => (Real.sqrt (d i) : 𝕜)))ᴴ * diagonal (fun i => (Real.sqrt (d i) : 𝕜))
      = LDL.diag hS := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, LDL.diag]
    congr 1; funext i
    rw [hd i, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hd0 i)]
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc LDL.lower hS * (diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        (diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ)
      = LDL.lower hS * ((diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        diagonal (fun i => (Real.sqrt (d i) : 𝕜))) * (LDL.lower hS)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [hsq, LDL.lower_conj_diag]

end Existence

section Existence2

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem star_mul_self_norm_div {x : 𝕜} (hx : x ≠ 0) :
    star ((‖x‖ : 𝕜) / x) * ((‖x‖ : 𝕜) / x) = 1 := by
  rw [star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm, RCLike.conj_mul, ← sq]
  exact div_self (pow_ne_zero 2 (by simpa using hx))

theorem exists_cholesky {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ B : Matrix n n 𝕜, ∃ a : n → ℝ, B.IsUpperTriangular ∧ (∀ i, 0 < a i) ∧
      (∀ i, B i i = a i) ∧ Bᴴ * B = S := by
  obtain ⟨R, hR, hRS⟩ := exists_isUpperTriangular_conjTranspose_mul_self hS
  have hdet : S.det ≠ 0 := (isUnit_iff_isUnit_det S).1 hS.isUnit |>.ne_zero
  have hRi : ∀ i, R i i ≠ 0 := by
    have : R.det ≠ 0 := by
      intro h; apply hdet; rw [← hRS, det_mul, h, mul_zero]
    rw [det_of_isUpperTriangular hR] at this
    exact fun i => Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)
  refine ⟨diagonal (fun i => (‖R i i‖ : 𝕜) / R i i) * R, fun i => ‖R i i‖,
    (blockTriangular_diagonal _).mul hR, fun i => norm_pos_iff.2 (hRi i), fun i => ?_, ?_⟩
  · rw [diagonal_mul, div_mul_cancel₀ _ (hRi i)]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _)ᴴ,
      diagonal_conjTranspose, diagonal_mul_diagonal]
    have : (fun i => (star (fun i => (‖R i i‖ : 𝕜) / R i i)) i * ((‖R i i‖ : 𝕜) / R i i)) =
        fun _ => 1 := funext fun i => star_mul_self_norm_div (hRi i)
    rw [this, diagonal_one, Matrix.one_mul, hRS]
end Existence2

end CompanionTheory.D.gk.admitted.CholeskyDecomposition
end

