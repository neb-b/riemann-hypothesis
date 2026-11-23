module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdClassGroupMk0EqOfLinearEquivPi
section
open scoped nonZeroDivisors

namespace GlobalTheory.DetClass

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mat {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i)) (a : (i : ι) → I i) :
    Matrix ι ι R := fun j i => (φ (Pi.single i (a i)) j : R)

theorem det_mem {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a : (i : ι) → I i) : (mat φ a).det ∈ ∏ j, J j := by
  rw [Matrix.det_apply]
  refine Ideal.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  have h : ∏ i, (mat φ a) (σ i) i ∈ ∏ i, J (σ i) :=
    Ideal.prod_mem_prod fun i _ => (φ (Pi.single i (a i)) (σ i)).2
  rwa [Equiv.prod_comp σ J] at h

theorem det_swap {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a b : (i : ι) → I i) :
    (∏ i, (b i : R)) * (mat φ a).det = (∏ i, (a i : R)) * (mat φ b).det := by
  have key : mat φ a * Matrix.diagonal (fun i => (b i : R))
      = mat φ b * Matrix.diagonal (fun i => (a i : R)) := by
    ext j i
    simp only [Matrix.mul_diagonal, mat]
    have h1 : (b i : R) • (Pi.single i (a i) : (k : ι) → I k)
        = (a i : R) • (Pi.single i (b i) : (k : ι) → I k) := by
      funext k
      by_cases hk : k = i
      · subst hk
        apply Subtype.ext
        simp [mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    have h2 := congrArg (fun x => ((φ x) j : R)) h1
    simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul] at h2
    rw [mul_comm, h2, mul_comm]
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  rw [mul_comm, h, mul_comm]

open Pointwise in
theorem span_mul_le {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (b : (i : ι) → I i) :
    Ideal.span {(mat φ b).det} * ∏ i, I i ≤ Ideal.span {∏ i, (b i : R)} * ∏ j, J j := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  have hP : ∏ i, I i = Submodule.span R (∏ i, (I i : Set R)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hP] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).mp hx
    have hs := det_swap φ (fun i => ⟨g i, hg (Finset.mem_univ i)⟩) b
    simp only at hs
    rw [mul_comm ((mat φ b).det), ← hs]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (det_mem φ _)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Ideal.add_mem _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r hx

theorem mat_mul {I J : ι → Ideal R} (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩) * mat φ.toLinearMap (fun i => ⟨c, hI i⟩)
      = Matrix.diagonal fun _ => c * c := by
  ext j k
  simp only [Matrix.mul_apply, mat, Matrix.diagonal_apply, LinearEquiv.coe_coe]
  set v := φ (Pi.single k ⟨c, hI k⟩) with hv
  have hsw : ∀ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l)
      = c • (Pi.single i (v i) : (l : ι) → J l) := by
    intro i
    funext l
    by_cases hl : l = i
    · subst hl
      apply Subtype.ext
      simp [mul_comm]
    · simp [Pi.single_eq_of_ne hl]
  have hsum : ∑ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l) = c • v := by
    simp_rw [hsw, ← Finset.smul_sum, Finset.univ_sum_single]
  have h := congrArg (fun x => ((φ.symm x) j : R)) hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hv, LinearEquiv.symm_apply_apply, Finset.sum_apply,
    Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] at h
  simp_rw [mul_comm _ ((v _ : J _) : R)]
  rw [h]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk]

theorem exists_span_mul_eq [IsDomain R] {I J : ι → Ideal R}
    (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hc0 : c ≠ 0) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * ∏ i, I i = Ideal.span {y} * ∏ i, J i := by
  set d : R := ∏ _i : ι, c with hd
  have h1 := span_mul_le φ.toLinearMap (fun i => ⟨c, hI i⟩)
  have h2 := span_mul_le φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)
  simp only at h1 h2
  rw [← hd] at h1 h2
  set x := (mat φ.toLinearMap (fun i => ⟨c, hI i⟩)).det
  set y := (mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)).det
  have hyx : y * x = d * d := by
    have h := congrArg Matrix.det (mat_mul φ c hI hJ)
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_mul_distrib] at h
    exact h
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => hc0
  have hdd : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hy0 : y ≠ 0 := fun h => hdd (by rw [← hyx, h, zero_mul])
  refine ⟨d * d, d * y, hdd, mul_ne_zero hd0 hy0, le_antisymm ?_ ?_⟩
  · rw [← hyx, ← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_comm (Ideal.span {d}), mul_assoc]
    exact Ideal.mul_mono_right h1
  · rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    exact Ideal.mul_mono_right h2

end GlobalTheory.DetClass


open GlobalTheory.DetClass in
theorem GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv (R : Type) [CommRing R] [IsDedekindDomain R]
    (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰)
    (h : Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R)))) :
    ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  classical
  obtain ⟨φ⟩ := h
  have hne : ∀ K : (Ideal R)⁰, ∃ e : R, e ∈ (K : Ideal R) ∧ e ≠ 0 := fun K =>
    Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero K)
  choose e he he0 using hne
  set c : R := (∏ i, e (I i)) * ∏ i, e (J i) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
    (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
  have hI : ∀ i, c ∈ (I i : Ideal R) := fun i =>
    Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  have hJ : ∀ i, c ∈ (J i : Ideal R) := fun i =>
    Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_span_mul_eq φ c hc0 hI hJ
  rw [← map_prod, ← map_prod, ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [Submonoid.coe_finsetProd] using hxy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRpowDecayIsBigOCocompact
section
open MeasureTheory

theorem GlobalTheory.prod_rpow_decay_isBigO_cocompact : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  intro ι _ g b hb hg
  classical
  choose C hC using hg
  have hC0 : ∀ i, 0 ≤ C i := fun i => by
    have h := hC i 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  refine Asymptotics.IsBigO.of_bound ((∏ i, C i) * n ^ b) ?_
  have hev : ∀ᶠ v : EuclideanSpace ℝ ι in Filter.cocompact _, 0 < ‖v‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop 0)
  filter_upwards [hev] with v hv
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : v = 0 := Subsingleton.elim _ _
    simp [this] at hv
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) Finset.univ_nonempty
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hnorm : ‖v‖ ≤ n * |v i₀| := by
    have h2 : ‖v‖ ^ 2 ≤ (n * |v i₀|) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v.ofLp i‖ ^ 2 ≤ ∑ _i : ι, |v i₀| ^ 2 := Finset.sum_le_sum fun i _ => by
              rw [Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hi₀ i (Finset.mem_univ _)) 2
        _ = n * |v i₀| ^ 2 := by simp [hn]
        _ ≤ (n * |v i₀|) ^ 2 := by
              rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hnpos : 0 < n := by linarith
  have hpos : 0 < ‖v‖ / n := by positivity
  have hle : ‖v‖ / n ≤ 1 + |v i₀| := by
    rw [div_le_iff₀ hnpos]; nlinarith [abs_nonneg (v i₀)]
  have hw : (1 + |v i₀|) ^ (-b) ≤ n ^ b * ‖v‖ ^ (-b) := by
    calc (1 + |v i₀|) ^ (-b) ≤ (‖v‖ / n) ^ (-b) := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      _ = n ^ b * ‖v‖ ^ (-b) := by
        rw [Real.div_rpow (norm_nonneg _) hnpos.le, Real.rpow_neg hnpos.le, div_inv_eq_mul, mul_comm]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖ ≤ ∏ i ∈ Finset.univ.erase i₀, C i :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (hC i (v i)).trans
      (mul_le_of_le_one_right (hC0 i)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (v i)]) (by linarith))))
  have h0 : ‖g i₀ (v i₀)‖ ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) :=
    (hC i₀ _).trans (mul_le_mul_of_nonneg_left hw (hC0 i₀))
  have hsplitg := Finset.mul_prod_erase Finset.univ (fun i => ‖g i (v i)‖) (Finset.mem_univ i₀)
  have hsplitC := Finset.mul_prod_erase Finset.univ C (Finset.mem_univ i₀)
  rw [norm_prod, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hsplitg, ← hsplitC]
  calc ‖g i₀ (v i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖
      ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) * ∏ i ∈ Finset.univ.erase i₀, C i :=
        mul_le_mul h0 hrest (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (mul_nonneg (hC0 i₀) (mul_nonneg (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = C i₀ * (∏ i ∈ Finset.univ.erase i₀, C i) * n ^ b * ‖v‖ ^ (-b) := by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdZpowMul
section
namespace GlobalTheory.LaurentFrac

theorem prod_zpow_mul {K : Type} [Field K] {I : Type} [Fintype I] (a : I → K) (N : I → ℤ)
    (ha : ∀ i, a i ≠ 0) :
    (∏ i, a i ^ N i) * ∏ i, a i ^ (-N i).toNat = ∏ i, a i ^ (N i).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ha i)]
  congr 1
  omega

theorem exists_frac (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (N : I → ℤ) (hs : ∀ i, θ (s i) ≠ 0) :
    ∃ x y : R, θ y ≠ 0 ∧
      (∏ i, algebraMap R (FractionRing R) (s i) ^ N i) * algebraMap R _ y = algebraMap R _ x ∧
      (∏ i, algebraMap V (FractionRing V) (θ (s i)) ^ N i) * algebraMap V _ (θ y)
        = algebraMap V _ (θ x) := by
  refine ⟨∏ i, s i ^ (N i).toNat, ∏ i, s i ^ (-N i).toNat, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_pow]
    exact pow_ne_zero _ (hs i)
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    have h : s i ≠ 0 := fun h => hs i (by rw [h, map_zero])
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i)

end GlobalTheory.LaurentFrac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplit
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_of_presentation_split
    (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (r : Fin m → Fin n → R) (hr : Submodule.span R (Set.range r) = LinearMap.ker π)
    (v : Fin n → Fin n → B) (w : Fin n → Fin m → B)
    (hv : ∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0)
    (hvw : ∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) :
    Module.Projective B (B ⊗[R] M) := by
  classical

  let φ : (Fin n → R) →ₗ[R] (Fin n → B) := ∑ a, (LinearMap.proj a).smulRight (v a)
  have hφ : ∀ x l, φ x l = ∑ a, algebraMap R B (x a) * v a l := by
    intro x l
    simp [φ, Finset.sum_apply, Algebra.smul_def]
  have hker : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hr, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext l
    rw [hφ]
    simpa using hv b l
  let ψ : M →ₗ[R] (Fin n → B) :=
    (LinearMap.ker π).liftQ φ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hψ : ∀ x, ψ (π x) = φ x := by
    intro x
    have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp [ψ, this]
  let i : B ⊗[R] M →ₗ[B] (Fin n → B) := ψ.liftBaseChange B
  let s : (Fin n → B) →ₗ[B] B ⊗[R] M :=
    ∑ l, (LinearMap.proj l).smulRight ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
  have hs : ∀ y, s y = ∑ l, y l • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) := by
    intro y; simp [s]
  have hsr : ∀ b, ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
    intro b
    have h0 : π (r b) = 0 := by
      rw [← LinearMap.mem_ker, ← hr]; exact Submodule.subset_span ⟨b, rfl⟩
    have : ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
        = (1 : B) ⊗ₜ[R] π (r b) := by
      conv_rhs => rw [show r b = ∑ l, r b l • Pi.single l (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, tmul_sum, algebraMap_smul, tmul_smul]
    rw [this, h0, tmul_zero]
  have hsv : ∀ a, s (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := by
    intro a
    rw [hs]
    simp_rw [hvw a, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ l, (w a b * algebraMap R B (r b l)) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
      intro b
      simp_rw [mul_smul, ← Finset.smul_sum, hsr, smul_zero]
    simp [this, ite_smul]
  have hsi : s ∘ₗ i = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    obtain ⟨z, rfl⟩ := hπ y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, i, LinearMap.liftBaseChange_tmul, map_smul]
    have hz : φ z = ∑ a, z a • v a := by
      funext l; rw [hφ]; simp [Finset.sum_apply, Algebra.smul_def]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hψ, hz, map_sum]
    simp_rw [LinearMap.map_smul_of_tower, hsv]
    conv_rhs => rw [show z = ∑ a, z a • Pi.single a (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_smul, TensorProduct.tmul_smul]
  exact Module.Projective.of_split i s hsi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective m
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm
  have hx : x = t := by
    have h := congr($hm (IsLocalRing.closedPoint _))
    have e₁ := Scheme.fromSpecResidueField_apply x
      (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))
    have e₂ := Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)
    exact e₁.symm.trans (h.trans e₂)
  subst hx
  rw [← Category.assoc, ← Spec.map_comp] at hm
  have hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]
    exact (Category.id_comp _).symm
  rw [eq_top_iff]
  intro y _
  have hy : K.subtype (φ.hom y) = y := congr($hφ y)
  rw [← hy]
  exact (φ.hom y).2


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.closure_range_residueFieldMap_pullback_eq_top (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom)
  let ι : CommRingCat.of L ⟶ (pullback f g).residueField t := CommRingCat.ofHom L.subtype
  let cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.fst f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  let cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.snd f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
  have hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t := rfl
  have hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t := rfl
  have hι : Mono ι := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have e : f (pullback.fst f g t) = g (pullback.snd f g t) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have key : f.residueFieldMap (pullback.fst f g t) ≫ cx =
      (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy := by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hcx, hcy]
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr pullback.condition t
  have hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f =
      (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g := by
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Spec.map_comp_assoc]
  have hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab =
      (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
    · rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
  exact _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientRetractPiQuotientOfSummand
section
universe u

namespace GlobalTheory

theorem quotient_retract_pi_quotient :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
      [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
      (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
      ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
        r ∘ₗ s = LinearMap.id := by
  intro C _ _ I H _ _ _ _ F hIF hEx
  obtain ⟨E', M, hc, hF⟩ := hEx
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' C H
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let P : H →ₗ[C] M := Submodule.linearProjOfIsCompl M E' hc.symm
  let q : H →ₗ[C] H := M.subtype ∘ₗ P
  have hPq : ∀ x, P (q x) = P x := fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm (P x)
  have hqq : ∀ x, q (q x) = q x := fun x => congrArg Subtype.val (hPq x)
  have hqE : ∀ x ∈ E', q x = 0 := fun x hx => by
    have h0 : P x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
    show ((P x : M) : H) = 0
    rw [h0]; rfl
  have hxq : ∀ x, x - q x ∈ F := by
    intro x
    rw [← hF]
    apply Submodule.mem_sup_left
    have h0 : P (x - q x) = 0 := by rw [map_sub, hPq, sub_self]
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).1 h0
  have hσπ : ∀ x, π (σ x) = x := fun x => LinearMap.congr_fun hσ x
  let s0 : H →ₗ[C] (Fin n → C ⧸ I) :=
    (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) ∘ₗ σ ∘ₗ q
  have hs0 : F ≤ LinearMap.ker s0 := by
    rw [← hF]
    refine sup_le (fun x hx => ?_) ?_
    · rw [LinearMap.mem_ker]
      show (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) (σ (q x)) = 0
      rw [hqE x hx, map_zero, map_zero]
    · refine Submodule.smul_le.2 (fun c hcI y _ => ?_)
      rw [LinearMap.mem_ker, map_smul]
      funext k
      show c • (Submodule.mkQ I (σ (q y) k)) = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.mul_mem_right _ hcI
  let s : (H ⧸ F) →ₗ[C] (Fin n → C ⧸ I) := F.liftQ s0 hs0
  let e : Fin n → (Fin n → C) := fun k j => if k = j then 1 else 0
  have hk : ∀ k, I ≤ LinearMap.ker (LinearMap.toSpanSingleton C (H ⧸ F) (F.mkQ (q (π (e k))))) := by
    intro k c hcI
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hIF (Submodule.smul_mem_smul hcI Submodule.mem_top)
  let g : Fin n → ((C ⧸ I) →ₗ[C] (H ⧸ F)) := fun k => I.liftQ _ (hk k)
  let r : (Fin n → C ⧸ I) →ₗ[C] (H ⧸ F) := ∑ k, g k ∘ₗ LinearMap.proj k
  refine ⟨n, s, r, ?_⟩
  apply Submodule.linearMap_qext
  ext x
  have h1 : r (s (F.mkQ x)) = F.mkQ (q (π (σ (q x)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.pi_apply_eq_sum_univ π (σ (q x)), map_sum, map_sum]
    simp only [r, s, g, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, Submodule.mkQ_apply, s0, LinearMap.pi_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LinearMap.toSpanSingleton_apply, map_smul, ← Submodule.Quotient.mk_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, hσπ, hqq]
  show F.mkQ (q x) = F.mkQ x
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]
  exact hxq x

end GlobalTheory
end

