module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LineDerivListEqIteratedFDeriv
section
open Filter Topology
open scoped ContDiff

namespace GlobalTheory

section Def

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def lineDerivList : List E → (E → V) → E → V
  | [], F => F
  | v :: l, F => fun z => lineDeriv 𝕜 (lineDerivList l F) z v

variable {𝕜}

theorem lineDerivList_cons (v : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 (v :: l) F = fun z => lineDeriv 𝕜 (lineDerivList 𝕜 l F) z v := rfl

theorem lineDerivList_append (l₁ l₂ : List E) (F : E → V) :
    lineDerivList 𝕜 (l₁ ++ l₂) F = lineDerivList 𝕜 l₁ (lineDerivList 𝕜 l₂ F) := by
  induction l₁ with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, lineDerivList_cons, ih]

theorem lineDerivList_const_smul (l : List E) (c : 𝕜) (F : E → V) :
    lineDerivList 𝕜 l (fun z => c • F z) = fun z => c • lineDerivList 𝕜 l F z := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv]
    exact deriv_fun_const_smul_field c _

@[simp] theorem lineDerivList_zero (l : List E) :
    lineDerivList 𝕜 l (fun _ => (0 : V)) = fun _ => 0 := by
  simpa using lineDerivList_const_smul l (0 : 𝕜) (fun _ => (0 : V))

theorem lineDerivList_comp_linearMap {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (L : E' →ₗ[𝕜] E) (l : List E') (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (L z)) = fun z => lineDerivList 𝕜 (l.map L) F (L z) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, List.map_cons, map_add (f := _), map_smul]

theorem lineDerivList_comp_add_const (c : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (z + c)) = fun z => lineDerivList 𝕜 l F (z + c) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, add_right_comm]

theorem lineDerivList_map_smul {κ : Type*} (c : κ → 𝕜) (e : κ → E) (l : List κ) (F : E → V) :
    lineDerivList 𝕜 (l.map fun k => c k • e k) F
      = fun z => (l.map c).prod • lineDerivList 𝕜 (l.map e) F z := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext z
    simp only [List.map_cons, lineDerivList_cons, ih, lineDeriv_smul, List.prod_cons, mul_smul]
    congr 1
    simp only [lineDeriv]
    exact deriv_fun_const_smul_field _ _

theorem lineDerivList_replicate (n : ℕ) (v : E) (F : E → V) (z : E) (t : 𝕜) :
    lineDerivList 𝕜 (List.replicate n v) F (z + t • v)
      = iteratedDeriv n (fun s : 𝕜 => F (z + s • v)) t := by
  induction n generalizing t with
  | zero => simp [lineDerivList]
  | succ n ih =>
    rw [List.replicate_succ, lineDerivList_cons, iteratedDeriv_succ]
    simp only [lineDeriv, add_assoc, ← add_smul, ih]
    rw [deriv_comp_const_add (f := iteratedDeriv n (fun s : 𝕜 => F (z + s • v))), add_zero]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem lineDerivList_congr {F G : E → V} {a : E} (h : F =ᶠ[𝓝 a] G) (l : List E) :
    lineDerivList 𝕜 l F =ᶠ[𝓝 a] lineDerivList 𝕜 l G := by
  induction l with
  | nil => exact h
  | cons v l ih =>
    filter_upwards [ih.eventuallyEq_nhds] with z hz
    exact hz.lineDeriv_eq

variable [CompleteSpace V]

theorem analyticAt_lineDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v : E) :
    AnalyticAt 𝕜 (fun z => lineDeriv 𝕜 F z v) a := by
  have h1 : AnalyticAt 𝕜 (fun z => fderiv 𝕜 F z v) a :=
    ((ContinuousLinearMap.apply 𝕜 V v).analyticAt _).comp h.fderiv
  refine h1.congr ?_
  filter_upwards [h.eventually_analyticAt] with z hz
  exact hz.differentiableAt.lineDeriv_eq_fderiv.symm

theorem analyticAt_lineDerivList {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    AnalyticAt 𝕜 (lineDerivList 𝕜 l F) a := by
  induction l with
  | nil => exact h
  | cons v l ih => exact analyticAt_lineDeriv ih v

theorem lineDerivList_ofFn {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {n : ℕ} (m : Fin n → E) :
    lineDerivList 𝕜 (List.ofFn m) F a = iteratedFDeriv 𝕜 n F a m := by
  induction n generalizing a with
  | zero => simp [lineDerivList]
  | succ n ih =>
    have hev : lineDerivList 𝕜 (List.ofFn fun i => m i.succ) F
        =ᶠ[𝓝 a] fun z => iteratedFDeriv 𝕜 n F z (Fin.tail m) := by
      filter_upwards [h.eventually_analyticAt] with z hz
      exact ih hz _
    have hd : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n F) a :=
      (h.contDiffAt (n := ω)).differentiableAt_iteratedFDeriv (by simp)
    rw [List.ofFn_succ, lineDerivList_cons, iteratedFDeriv_succ_apply_left]
    dsimp only
    rw [(analyticAt_lineDerivList h _).differentiableAt.lineDeriv_eq_fderiv, hev.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hd]

theorem lineDerivList_eq_iteratedFDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    lineDerivList 𝕜 l F a = iteratedFDeriv 𝕜 l.length F a l.get := by
  rw [← lineDerivList_ofFn h, List.ofFn_get]

theorem lineDerivList_swap {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v w : E) :
    lineDerivList 𝕜 [v, w] F a = lineDerivList 𝕜 [w, v] F a := by
  have h1 := lineDerivList_ofFn h ![v, w]
  have h2 := lineDerivList_ofFn h ![w, v]
  have h3 := (h.contDiffAt (n := ω)).iteratedFDeriv_comp_perm ![v, w] (Equiv.swap 0 1)
  have h4 : ![v, w] ∘ (Equiv.swap (0 : Fin 2) 1) = ![w, v] := by
    funext i; fin_cases i <;> simp
  rw [h4] at h3
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h1 h2
  rw [h1, h2, h3]

theorem lineDerivList_perm {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List E}
    (hl : l₁.Perm l₂) : lineDerivList 𝕜 l₁ F a = lineDerivList 𝕜 l₂ F a := by
  induction hl generalizing a with
  | nil => rfl
  | cons v _ ih =>
    refine Filter.EventuallyEq.lineDeriv_eq ?_
    filter_upwards [h.eventually_analyticAt] with z hz
    exact ih hz
  | swap v w l => exact lineDerivList_swap (analyticAt_lineDerivList h l) w v
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

theorem lineDerivList_add {F G : E → V} {a : E} (hF : AnalyticAt 𝕜 F a) (hG : AnalyticAt 𝕜 G a)
    (l : List E) :
    lineDerivList 𝕜 l (fun z => F z + G z) a
      = lineDerivList 𝕜 l F a + lineDerivList 𝕜 l G a := by
  have hFG : AnalyticAt 𝕜 (fun z => F z + G z) a := hF.add hG
  rw [lineDerivList_eq_iteratedFDeriv hFG, lineDerivList_eq_iteratedFDeriv hF,
    lineDerivList_eq_iteratedFDeriv hG,
    fun_iteratedFDeriv_add_apply (hF.contDiffAt) (hG.contDiffAt)]
  rfl

theorem lineDerivList_sum {κ : Type*} (s : Finset κ) {F : κ → E → V} {a : E}
    (hF : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a) (l : List E) :
    lineDerivList 𝕜 l (fun z => ∑ k ∈ s, F k z) a = ∑ k ∈ s, lineDerivList 𝕜 l (F k) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    rw [lineDerivList_add (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_sum _ hs),
      ih hs]

end Analytic

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralProdPartialSums
section
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat

namespace GlobalTheory.FlagVolume

theorem lintegral_radial {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal ((2 * (m + 1) * A ^ (m + 1))⁻¹) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹)
      (r * ((A + r ^ 2) ^ (m + 2))⁻¹) r := by
    intro r _
    have hp : 0 < A + r ^ 2 := by positivity
    have h1 : HasDerivAt (fun r : ℝ ↦ A + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add A
    have h2 := ((h1.pow (m + 1)).const_mul (2 * ((m : ℝ) + 1))).fun_inv
      (show 2 * ((m : ℝ) + 1) * (A + r ^ 2) ^ (m + 1) ≠ 0 by positivity)
    refine h2.fun_neg.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((A + r ^ 2) ^ (m + 2))⁻¹ := fun r hr ↦ by
    have : 0 < r := hr
    positivity
  have hl : Tendsto (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine Tendsto.neg (Tendsto.inv_tendsto_atTop ?_)
    refine Tendsto.const_mul_atTop (by change (0 : ℝ) < 2 * ((m : ℝ) + 1); positivity) ?_
    exact (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hnn hl)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)),
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hl]
  simp

theorem lintegral_complex_inv_pow {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal (π / (m + 1) * (A ^ (m + 1))⁻¹) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      ENNReal.ofReal (((A + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal (p.1 * ((A + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ ↦ (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul (le_of_lt hp.1)]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ ↦ ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ ↦ (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop), lintegral_radial hA]
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

theorem lintegral_fin_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ z : ℂ, ∫⁻ w : Fin n → ℂ, f (Fin.cons z w) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod
    (fun a ↦ f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm a))
    (hf.comp h.measurable).aemeasurable]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_inv_pow (n : ℕ) : ∀ (m : ℕ) {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((A + ∑ k, ‖z k‖ ^ 2) ^ (m + n + 1))⁻¹) =
      ENNReal.ofReal (π ^ n * m ! / (m + n)! * (A ^ (m + 1))⁻¹) := by
  induction n with
  | zero =>
    intro m A hA
    have : (m ! : ℝ) ≠ 0 := by positivity
    simp [volume_pi, this]
  | succ n ih =>
    intro m A hA
    rw [lintegral_fin_succ (by fun_prop)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2 + ∑ k, ‖w k‖ ^ 2) ^ (m + n + 1 + 1))⁻¹) =
        ENNReal.ofReal (π ^ n * (m + 1)! / (m + 1 + n)!) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := fun z ↦ by
      rw [← ENNReal.ofReal_mul (by positivity), ← ih (m + 1) (by positivity),
        show m + 1 + n = m + n + 1 by ring]
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), show m + 1 + n = m + n + 1 by ring,
      Nat.factorial_succ m]
    congr 1
    push_cast
    field_simp
    ring

theorem lintegral_comp_vecMul {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ)
    (hR : R.det ≠ 0) {f : (n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, f b = ENNReal.ofReal (‖R.det‖ ^ 2) * ∫⁻ y, f (Matrix.vecMul y R) := by
  let T : (n → ℂ) →ₗ[ℝ] (n → ℂ) := (Matrix.toLin' R.transpose).restrictScalars ℝ
  have hT : LinearMap.det T = ‖R.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (n → ℂ))
    (f := T) (hT ▸ hp.ne')
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have h1 : ∫⁻ y, f (Matrix.vecMul y R) = ∫⁻ y, f (T y) := by
    simp [T, Matrix.mulVec_transpose]
  rw [h1, ← lintegral_map hf hTm, hmap, lintegral_smul_measure, hT, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le, abs_of_pos (inv_pos.2 hp), mul_inv_cancel₀ hp.ne']
  simp

end GlobalTheory.FlagVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
section
open Matrix

namespace GlobalTheory

section Ring

variable {R : Type*} [CommRing R]

abbrev subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) : Fin i → n :=
  S.1.orderEmbOfFin S.2

theorem range_subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) :=
  Finset.range_orderEmbOfFin _ _

theorem subsetEnum_injective {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Function.Injective (subsetEnum S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem alternatingMap_apply_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (f : (n → R) [⋀^Fin i]→ₗ[R] M)
    (A : Fin i → n → R) :
    f A = ∑ S : Set.powersetCard n i,
      ((Matrix.of A).submatrix id (subsetEnum S)).det • f (fun a => Pi.single (subsetEnum S a) 1) := by
  classical
  let b := Pi.basisFun R n
  have h := (b.exteriorPower i).sum_repr (exteriorPower.ιMulti R i A)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f A, ← h, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_smul, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  congr 2
  ext a
  simp [b, subsetEnum, Set.powersetCard.ofFinEmbEquiv_symm_apply, Pi.basisFun_apply]

theorem det_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by
  classical
  have h := alternatingMap_apply_eq_sum_minors
    ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A
  have h0 : (A * B).det =
      ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A := rfl
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [AlternatingMap.compLinearMap_apply]
  change Matrix.det _ = _
  congr 1
  ext a c
  simp [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]

theorem det_mul_det_eq_of_range_eq {m k n : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix m n R) (B : Matrix n m R) (φ : k ≃ m) (e : m → n) (g : k → n)
    (hg : Function.Injective g) (h : Set.range e = Set.range g) :
    (A.submatrix id e).det * (B.submatrix e id).det =
      (A.submatrix φ g).det * (B.submatrix g φ).det := by
  have h1 : ∀ a : k, ∃ c : m, e c = g a := fun a => by
    have : g a ∈ Set.range e := h ▸ Set.mem_range_self a
    exact this
  choose s hs using h1
  have hinj : Function.Injective (φ.symm ∘ s) := by
    intro a a' haa
    have : s a = s a' := φ.symm.injective haa
    exact hg (by rw [← hs a, ← hs a', this])
  let σ : Equiv.Perm k := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ a, e (φ (σ a)) = g a := fun a => by simp [σ, hs]
  have hA : A.submatrix φ g = ((A.submatrix id e).submatrix φ φ).submatrix id σ := by
    ext a c; simp [hσ]
  have hB : B.submatrix g φ = ((B.submatrix e id).submatrix φ φ).submatrix σ id := by
    ext a c; simp [hσ]
  rw [hA, hB, det_permute, det_permute', det_submatrix_equiv_self, det_submatrix_equiv_self]
  have : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  linear_combination (-(A.submatrix id e).det * (B.submatrix e id).det) * this

theorem det_mul_eq_sum_minors_of_enum {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (e : Set.powersetCard n (Fintype.card m) → m → n)
    (he : ∀ S, Set.range (e S) = (S.1 : Set n)) (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ S : Set.powersetCard n (Fintype.card m),
      (A.submatrix id (e S)).det * (B.submatrix (e S) id).det := by
  classical
  letI : LinearOrder n := linearOrderOfSTO WellOrderingRel
  let φ : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  rw [← det_submatrix_equiv_self φ (A * B), submatrix_mul A B φ id φ Function.bijective_id,
    det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [det_mul_det_eq_of_range_eq A B φ (e S) (subsetEnum S) (subsetEnum_injective S)
    ((he S).trans (range_subsetEnum S).symm)]
  rfl

theorem det_submatrix_mul_eq_sum_minors {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [submatrix_mul A B r id c Function.bijective_id, det_mul_eq_sum_minors]
  rfl

theorem det_mul_diagonal_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (d : n → R) (B : Matrix n (Fin i) R) :
    (A * diagonal d * B).det = ∑ S : Set.powersetCard n i,
      (∏ s ∈ S.1, d s) *
        ((A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det) := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (A * diagonal d).submatrix id (subsetEnum S) =
      A.submatrix id (subsetEnum S) * diagonal (d ∘ subsetEnum S) := by
    ext a c; simp
  have h2 : ∏ a, d (subsetEnum S a) = ∏ s ∈ S.1, d s := by
    refine Finset.prod_bij (fun a _ => subsetEnum S a) (fun a _ => Finset.orderEmbOfFin_mem _ _ _)
      (fun a _ b _ h => subsetEnum_injective S h) (fun s hs => ?_) (fun _ _ => rfl)
    have : s ∈ Set.range (subsetEnum S) := by rw [range_subsetEnum]; exact hs
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_univ _, ha⟩
  rw [h1, det_mul, det_diagonal, ← h2]
  simp only [Function.comp_apply]
  ring

end Ring

section Normed

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}

theorem det_mul_conjTranspose_eq_sum_norm_sq (A : Matrix (Fin i) n 𝕜) :
    (A * Aᴴ).det =
      ((∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_minors]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]

theorem sum_norm_sq_minors_eq_one (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq A
  rw [hA, det_one] at h
  exact_mod_cast h.symm

theorem two_rpow_neg_half_le_choose_rpow {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < N.choose i := by exact_mod_cast Nat.choose_pos hi
  have hle : (N.choose i : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.choose_le_two_pow N i).trans (Nat.pow_le_pow_right two_pos hr)
  calc (2 : ℝ) ^ (-(r : ℝ) / 2) = ((2 : ℝ) ^ (r : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)

theorem exists_choose_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by
  have h := sum_norm_sq_minors_eq_one A hA
  have hne : (Finset.univ : Finset (Set.powersetCard n i)).Nonempty := by
    rcases (Finset.univ : Finset (Set.powersetCard n i)).eq_empty_or_nonempty with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hi : i ≤ Fintype.card n := by
    obtain ⟨S, -⟩ := hne
    exact S.2 ▸ Finset.card_le_univ S.1
  have hcard : Fintype.card (Set.powersetCard n i) = (Fintype.card n).choose i := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hpos : (0 : ℝ) < (Fintype.card n).choose i := by exact_mod_cast Nat.choose_pos hi
  refine ⟨hi, ?_⟩
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (((Fintype.card n).choose i : ℝ))⁻¹)
    (g := fun S => ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2) (by
      rw [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])
  refine ⟨S, (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_⟩
  refine le_of_eq_of_le ?_ hS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
  norm_num

theorem exists_two_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by
  obtain ⟨hi, S, hS⟩ := exists_choose_rpow_le_norm_minor A hA
  exact ⟨S, (two_rpow_neg_half_le_choose_rpow hi hr).trans hS⟩

end Normed

end GlobalTheory
end

