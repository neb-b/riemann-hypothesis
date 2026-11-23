module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeParametrization
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW.DualLattice

noncomputable def ratBasis {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) : Module.Basis κ ℚ F :=
  b.localizationLocalization ℚ (nonZeroDivisors ℤ) F

theorem ratBasis_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) (v : κ) : ratBasis b v = (b v : F) := by
  simp [ratBasis, Module.Basis.localizationLocalization_apply]

theorem exists_trace_dual {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (b : Module.Basis κ ℤ (𝓞 F)) :
    ∃ d : κ → F, ∀ v u, Algebra.trace ℚ F ((b v : F) * d u) = if v = u then 1 else 0 := by
  classical
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨fun u => (Algebra.traceForm ℚ F).dualBasis hnd (ratBasis b) u, fun v u => ?_⟩
  have h := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ F) hnd
    (ratBasis b) u v
  rw [Algebra.traceForm_apply, ratBasis_apply, mul_comm] at h
  exact h

theorem eq_of_trace_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) {x y : F}
    (h : ∀ v, Algebra.trace ℚ F ((b v : F) * x) = Algebra.trace ℚ F ((b v : F) * y)) :
    x = y := by
  have hnd := traceForm_nondegenerate ℚ F
  rw [← sub_eq_zero]
  apply hnd.2 _
  intro z
  have hL : (Algebra.trace ℚ F) ∘ₗ (LinearMap.mulRight ℚ (x - y)) = 0 := by
    refine (ratBasis b).ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ratBasis_apply, mul_sub, map_sub, h v,
      sub_self, LinearMap.zero_apply]
  exact LinearMap.congr_fun hL z

theorem exists_dual_param (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ)
    (hB : B.det ≠ 0) (hN : 0 < N) :
    ∃ e : (ι × InfinitePlace F → ℤ) → ι → F,
      (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧
      ∀ y : ι → F, (∀ i v, ∃ m : ℤ,
        (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by
  classical
  obtain ⟨d, hd⟩ := exists_trace_dual b
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBB : ∀ c : ι → F, B *ᵥ (B⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have hinj : ∀ y : ι → F, B⁻¹ *ᵥ (B *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec]
  obtain ⟨c, hc⟩ : ∃ c : (ι × InfinitePlace F → ℤ) → ι → F,
      ∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c n i) = n (i, v) := by
    refine ⟨fun n i => ∑ u, algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u, fun n i v => ?_⟩
    have : Algebra.trace ℚ F ((b v : F) * ∑ u, algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u)
        = (n (i, v) : ℚ) / N := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.mul_sum, map_sum]
      have hterm : ∀ u, Algebra.trace ℚ F ((b v : F) * (algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u))
          = ((n (i, u) : ℚ) / N) * (if v = u then 1 else 0) := by
        intro u
        rw [mul_left_comm, ← Algebra.smul_def, map_smul, hd, smul_eq_mul]
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      simp
    simp only [this]
    field_simp
  refine ⟨fun n => B⁻¹ *ᵥ c n, fun n i v => ?_, fun y hy => ?_⟩
  · simp only [hBB]
    exact hc n i v
  · choose m hm using hy
    refine ⟨fun p => m p.1 p.2, ?_⟩
    have hcy : c (fun p => m p.1 p.2) = B *ᵥ y := by
      funext i
      exact eq_of_trace_eq b fun v =>
        mul_left_cancel₀ hNq ((hc (fun p => m p.1 p.2) i v).trans (hm i v).symm)
    change B⁻¹ *ᵥ c (fun p => m p.1 p.2) = y
    rw [hcy, hinj]

end GlobalTheory.CompanionTheory.SW.ThW.DualLattice
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteFieldQuadraticFormPointCount
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.QuadricCount

open ComplexConjugate

variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def quadForm (B : Matrix ι ι k) (x : ι → k) : k :=
  (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x))

theorem quadForm_add (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k} (hB : B.IsSymm) (y z : ι → k) :
    quadForm B (y + z) = quadForm B y + quadForm B z + y ⬝ᵥ (B *ᵥ z) := by
  have hs : z ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  unfold quadForm
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hs]
  field_simp
  ring

theorem sum_char_dot (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {w : ι → k} (hw : w ≠ 0) :
    ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨c, hc⟩ := (AddChar.ne_one_iff).mp hψ
  have hi' : w i ≠ 0 := hi
  have he : (Pi.single i (c / w i) : ι → k) ⬝ᵥ w = c := by
    rw [single_dotProduct]
    field_simp
  have hS : ψ c * ∑ y : ι → k, ψ (y ⬝ᵥ w) = ∑ y : ι → k, ψ (y ⬝ᵥ w) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (Pi.single i (c / w i) : ι → k)) _ _ ?_
    intro x
    rw [Equiv.coe_addRight, add_dotProduct, he, AddChar.map_add_eq_mul, mul_comm]
  have h0 : (ψ c - 1) * ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
    rw [sub_mul, hS, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

theorem gauss_mul_conj (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {t : k} (ht : t ≠ 0) :
    (∑ x, ψ (t * quadForm B x)) * conj (∑ x, ψ (t * quadForm B x)) =
      (Fintype.card k : ℂ) ^ Fintype.card ι := by
  classical
  have inner : ∀ z : ι → k, ∑ y : ι → k, ψ (t * (y ⬝ᵥ (B *ᵥ z))) =
      if z = 0 then (Fintype.card k : ℂ) ^ Fintype.card ι else 0 := by
    intro z
    split_ifs with hz
    · subst hz
      simp
    · have hw : t • (B *ᵥ z) ≠ 0 := by
        intro h
        have h' : B *ᵥ z = 0 := (smul_eq_zero.mp h).resolve_left ht
        exact hz (Matrix.eq_zero_of_mulVec_eq_zero hdet h')
      have := sum_char_dot ψ hψ hw
      simpa [dotProduct_smul, smul_eq_mul] using this
  have step : ∀ y : ι → k, ∑ x, ψ (t * quadForm B x) * conj (ψ (t * quadForm B y)) =
      ∑ z, ψ (t * quadForm B z) * ψ (t * (y ⬝ᵥ (B *ᵥ z))) := by
    intro y
    refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_).symm
    intro z
    rw [Equiv.coe_addLeft, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, quadForm_add h2 hB]
    congr 1
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inner]
  simp [quadForm]

theorem norm_gauss (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ} (hM : Fintype.card ι = 2 * M) {t : k}
    (ht : t ≠ 0) : ‖∑ x, ψ (t * quadForm B x)‖ = (Fintype.card k : ℝ) ^ M := by
  have h := gauss_mul_conj ψ hψ h2 hB hdet ht
  rw [Complex.mul_conj', hM] at h
  have h' : ‖∑ x, ψ (t * quadForm B x)‖ ^ 2 = ((Fintype.card k : ℝ) ^ M) ^ 2 := by
    rw [← pow_mul, mul_comm M 2]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

theorem count_mul_card (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (B : Matrix ι ι k) (s : k) :
    (Nat.card {x : ι → k // quadForm B x = s} : ℂ) * (Fintype.card k : ℂ) =
      ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
  classical
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have h1 : ∀ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) =
      if quadForm B x = s then (Fintype.card k : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift _ hprim]
    simp [sub_eq_zero]
  have h2 : ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) =
      ∑ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h2]
  simp_rw [h1]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul]

theorem card_quadric_even (k : Type) [Field k] [Fintype k] (hchar : ringChar k ≠ 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  have hbound : ‖∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    have hterm : ∀ t ∈ Finset.univ.erase (0 : k),
        ‖ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤ (Fintype.card k : ℝ) ^ M := by
      intro t ht
      rw [norm_mul, AddChar.norm_apply, one_mul,
        norm_gauss ψ hψ1 h2 hB hdet hM (Finset.ne_of_mem_erase ht)]
    have := norm_sum_le_of_le _ hterm
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
    simp
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) =
      ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hbound
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq] at habs
  have hqM : (0 : ℝ) ≤ (Fintype.card k : ℝ) ^ M := by positivity
  have hfin : |(N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| * (Fintype.card k : ℝ) ≤
      (Fintype.card k : ℝ) ^ M * (Fintype.card k : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_right hfin hq

theorem quadric_count_even : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M :=
  fun k _ _ h ι _ _ M hM hM1 B hB hd s => card_quadric_even k h ι M hM hM1 B hB hd s

end GlobalTheory.CompanionTheory.SW.QuadricCount
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianChangeOfVariablesIsometry
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.GaussOrth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem quad_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (g M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ x)) = x ⬝ᵥ ((gᵀ * M * g) *ᵥ x) := by
  have h : (gᵀ * M * g) *ᵥ x = gᵀ *ᵥ (M *ᵥ (g *ᵥ x)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h, Matrix.dotProduct_mulVec x gᵀ, Matrix.vecMul_transpose]

theorem abs_det_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {g M : Matrix ι ι ℝ}
    (hM : M.det ≠ 0) (h : gᵀ * M * g = M) : |g.det| = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : g.det * g.det = 1 := by
    apply mul_right_cancel₀ hM
    rw [one_mul]
    calc g.det * g.det * M.det = g.det * M.det * g.det := by ring
      _ = M.det := h1
  have h3 : |g.det| * |g.det| = 1 := by rw [← abs_mul, h2, abs_one]
  have h4 : 0 ≤ |g.det| := abs_nonneg _
  nlinarith [sq_nonneg (|g.det| - 1), sq_nonneg (|g.det| + 1)]

theorem measurePreserving_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℝ}
    (h : |g.det| = 1) : MeasurePreserving (fun x : ι → ℝ => g *ᵥ x) volume volume := by
  have hd : g.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    exact zero_ne_one h
  refine ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, ?_⟩
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  have e : (fun x : ι → ℝ => g *ᵥ x) = ⇑(Matrix.toLin' g) := by
    ext x i
    simp [Matrix.toLin'_apply]
  rw [e, this, abs_inv, h]
  simp

theorem measurableEmbedding_mulVec {W ι : Type} [Fintype W] [Fintype ι] [DecidableEq ι]
    {g : W → Matrix ι ι ℝ} (h : ∀ w, (g w).det ≠ 0) :
    MeasurableEmbedding (fun (x : W → ι → ℝ) (w : W) => g w *ᵥ x w) := by
  have hu : ∀ w, IsUnit (g w).det := fun w => isUnit_iff_ne_zero.mpr (h w)
  let e : (W → ι → ℝ) ≃ᵐ (W → ι → ℝ) :=
    { toFun := fun x w => g w *ᵥ x w
      invFun := fun x w => (g w)⁻¹ *ᵥ x w
      left_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu w), Matrix.one_mulVec]
      right_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mulVec]
      measurable_toFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w)
      measurable_invFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w) }
  exact e.measurableEmbedding

theorem gauss_orth {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧
    ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by
  have first : ∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x := by
    intro τ x
    unfold gauss
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [quad_mulVec, quad_mulVec, hg w]
  refine ⟨first, fun τ => ?_⟩
  have hdet : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := (RingHom.map_det (ρ w) B).symm
    rw [e]
    exact (map_ne_zero (ρ w)).mpr hB
  have habs : ∀ w, |(gi w).det| = 1 := fun w => abs_det_eq_one (hdet w) (hg w)
  have hne : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have := habs w
    rw [h0, abs_zero] at this
    exact zero_ne_one this
  have hmp : MeasurePreserving (fun (x : InfinitePlace F → ι → ℝ) w => gi w *ᵥ x w)
      volume volume :=
    volume_preserving_pi fun w => measurePreserving_mulVec (habs w)
  have hint := hmp.integral_comp (measurableEmbedding_mulVec hne) (gauss B ρ P τ)
  unfold cG
  rw [← hint]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (first τ x).symm)

end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth

theorem GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (ρ : NumberField.InfinitePlace F → (F →+* ℝ)) (P : NumberField.InfinitePlace F → Matrix ι ι ℝ) (gi : NumberField.InfinitePlace F → Matrix ι ι ℝ), B.det ≠ 0 → (∀ w, (gi w).transpose * B.map (ρ w) * gi w = B.map (ρ w)) → (∀ (τ : NumberField.InfinitePlace F → ℂ) (x : NumberField.InfinitePlace F → ι → ℝ), GlobalTheory.CompanionTheory.SW.Core.gauss B ρ P τ (fun w => (gi w).mulVec (x w)) = GlobalTheory.CompanionTheory.SW.Core.gauss B ρ (fun w => (gi w).transpose * P w * gi w) τ x) ∧ ∀ τ : NumberField.InfinitePlace F → ℂ, GlobalTheory.CompanionTheory.SW.Core.cG B ρ (fun w => (gi w).transpose * P w * gi w) τ = GlobalTheory.CompanionTheory.SW.Core.cG B ρ P τ :=
  fun _ _ _ _ _ _ B ρ P gi hB hg => GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth B ρ P gi hB hg
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramTransposeDualTraceIdentity
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (y : ι → F) : DM B ρ *ᵥ emb ρ y = emb ρ (B *ᵥ y) := by
  funext p
  obtain ⟨i, w⟩ := p
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul]

theorem gM_transpose_mulVec {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) (z : ι × InfinitePlace F → ℝ) (i : ι)
    (v : InfinitePlace F) :
    ((gM ρ b N)ᵀ *ᵥ z) (i, v) = (N : ℝ) * ∑ w, ρ w (b v : F) * z (i, w) := by
  simp only [mulVec, dotProduct, gM, transpose_apply, Matrix.smul_apply, kroneckerMap_apply, EM,
    Matrix.one_apply, Fintype.sum_prod_type, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Finset.sum_ite_eq, mul_assoc]

theorem gM_DM_emb_eq_trace : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  intro F _ _ ι _ _ _ M B ρ P hQ b N y
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  funext p
  obtain ⟨i, v⟩ := p
  rw [DM_mulVec_emb, gM_transpose_mulVec]
  have h := sum_rho_eq_trace hT hρ ((b v : F) * (B *ᵥ y) i)
  simp only [emb, ← map_mul]
  rw [h]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroups
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.HaarTransport

theorem map_addEquiv_haar (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup V'] [TopologicalSpace V'] [LocallyCompactSpace V']
    [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V']
    [IsTopologicalAddGroup V'] (μ : Measure V) [μ.IsAddHaarMeasure] (μ' : Measure V')
    [μ'.IsAddHaarMeasure] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm) :
    (∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ') ∧
      ∀ (L : Set V) (L' : Set V'), IsCompact L → IsOpen L → L.Nonempty →
        (∀ v, e v ∈ L' ↔ v ∈ L) → μ L = μ' L' → μ.map e = μ' := by
  let E : V ≃ₜ+ V' := { e with continuous_toFun := he, continuous_invFun := hes }
  haveI hH : (μ.map e).IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  have ha := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ'
  have ha0 : Measure.addHaarScalarFactor (μ.map e) μ' ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  generalize Measure.addHaarScalarFactor (μ.map e) μ' = a at ha ha0
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.mk e.toEquiv he hes).measurableEmbedding
  refine ⟨⟨a, ha0, ha⟩, ?_⟩
  · intro L L' hLc hLo hLn hL hmass
    have hpre : e ⁻¹' L' = L := by ext v; exact hL v
    have hpos : μ L ≠ 0 := (hLo.measure_pos μ hLn).ne'
    have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
    have hLm : μ.map e L' = μ L := by
      rw [hemb.map_apply, hpre]
    have hval : μ L = (a : ℝ≥0∞) * μ L := by
      have h1 := congrArg (fun m => m L') ha
      simp only [Measure.smul_apply, hLm] at h1
      rw [← hmass] at h1
      simpa [ENNReal.smul_def] using h1
    have ha1 : (a : ℝ≥0∞) = 1 := by
      have h2 : (a : ℝ≥0∞) * μ L = 1 * μ L := by rw [one_mul]; exact hval.symm
      exact (ENNReal.mul_left_inj hpos hfin).1 h2
    have ha1' : a = 1 := by exact_mod_cast ha1
    rw [ha, ha1', one_smul]

end GlobalTheory.CompanionTheory.SW.HaarTransport
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExists
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem exists_integralBasis_infinitePlace (F : Type) [Field F] [NumberField F]
    (hF : IsTotallyReal F) : Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have h2 : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ InfinitePlace F :=
    Fintype.equivOfCardEq (by
      rw [hcard, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank])
  exact ⟨(RingOfIntegers.basis F).reindex e⟩

end GlobalTheory.CompanionTheory.SW.ThW
end

