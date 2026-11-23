module

public import Mathlib
public import GroundTheory.AutomorphicForms.RealGroupsLie
public import GroundTheory.AutomorphicForms.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0003

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinBasic
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem expG_add_smul (X : 𝔤) (s t : ℝ) :
    h.expG ((s + t) • X) = h.expG (s • X) * h.expG (t • X) := by
  apply Subtype.ext; apply Units.ext
  simp only [coe_expG, Submodule.coe_smul, Subgroup.coe_mul, Units.val_mul, add_smul]
  exact exp_add_of_commute' ℝ ((Commute.refl (X : 𝔸)).smul_left s |>.smul_right t)

noncomputable def prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) : G :=
  (List.ofFn fun i => h.expG (t i • X i)).prod

theorem chart_self (g : G) : h.chart g g = 0 := by
  show subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (((g⁻¹ * g : G) : 𝔸ˣ) : 𝔸)) = 0
  simp [expPartialHomeomorph_symm_one]

theorem contMDiffAt_iff_expG {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {n : WithTop ℕ∞} {f : G → E'} {g : G} :
    (letI := h.chartedSpace; ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, E') n f g) ↔
      ContDiffAt ℝ n (fun Y : 𝔤 => f (g * h.expG Y)) 0 := by
  let := h.chartedSpace
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have e1 : (extChartAt 𝓘(ℝ, 𝔤) g) g = 0 := by
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    exact h.chart_self g
  have e2 : f ∘ (extChartAt 𝓘(ℝ, 𝔤) g).symm = fun Y : 𝔤 => f (g * h.expG Y) := by
    funext Y
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id]
    rfl
  rw [e1, e2, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]


include h in
theorem locallyCompactSpace : LocallyCompactSpace G := by
  let := h.chartedSpace
  exact ChartedSpace.locallyCompactSpace 𝔤 G

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HermitianSpaces
section
namespace GroundTheory.Automorphic

open Module Matrix

section MatrixGroup

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]

def unitaryGroupMatrix (s : A →+* A) (H : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | ((g : Matrix ι ι A).map s)ᵀ * H * g = H}
  one_mem' := by
    simp [Matrix.map_one _ (map_zero s) (map_one s)]
  mul_mem' {g k} hg hk := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Units.val_mul, Matrix.map_mul, transpose_mul]
    calc _ = ((k : Matrix ι ι A).map s)ᵀ *
          ((((g : Matrix ι ι A).map s)ᵀ * H * g) * k) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hg, ← Matrix.mul_assoc, hk]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((g : Matrix ι ι A).map s) * ((↑g⁻¹ : Matrix ι ι A).map s) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero s) (map_one s)]
    calc ((↑g⁻¹ : Matrix ι ι A).map s)ᵀ * H * ↑g⁻¹
        = ((↑g⁻¹ : Matrix ι ι A).map s)ᵀ * (((g : Matrix ι ι A).map s)ᵀ * H * g) * ↑g⁻¹ := by
          rw [hg]
      _ = (((g : Matrix ι ι A).map s) * ((↑g⁻¹ : Matrix ι ι A).map s))ᵀ * H *
          ((g : Matrix ι ι A) * ↑g⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [h1, Units.mul_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_unitaryGroupMatrix {s : A →+* A} {H : Matrix ι ι A} {g : GL ι A} :
    g ∈ unitaryGroupMatrix s H ↔ ((g : Matrix ι ι A).map s)ᵀ * H * g = H := Iff.rfl

theorem isUnit_det_of_unitary (s : A →+* A) {H : Matrix ι ι A} (hH : IsUnit H.det)
    {M : Matrix ι ι A} (hM : (M.map s)ᵀ * H * M = H) : IsUnit M.det := by
  have hd := congrArg Matrix.det hM
  have hs : (M.map s).det = s M.det := (RingHom.map_det s M).symm
  rw [det_mul, det_mul, det_transpose, hs] at hd
  have h2 : M.det * s M.det = 1 := by
    apply hH.mul_left_cancel
    linear_combination hd
  exact IsUnit.of_mul_eq_one _ h2

theorem exists_mem_unitaryGroupMatrix_iff (s : A →+* A) {H : Matrix ι ι A} (hH : IsUnit H.det)
    (M : Matrix ι ι A) :
    (∃ g ∈ unitaryGroupMatrix s H, (g : Matrix ι ι A) = M) ↔ (M.map s)ᵀ * H * M = H := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hM
    exact ⟨nonsingInvUnit M (isUnit_det_of_unitary s hH hM), hM, rfl⟩

def IsHermitianFor (s : A →+* A) (H : Matrix ι ι A) : Prop := (H.map s)ᵀ = H

end MatrixGroup

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

noncomputable abbrev conjHom : E →+* E := (conj F E).toAlgHom.toRingHom

variable (V : Type*) [AddCommGroup V] [Module E V]

structure HermitianForm where

  toSesq : V →ₛₗ[conjHom F E] V →ₗ[E] E

  isSymm : toSesq.IsSymm

  nonsingular : Function.Bijective toSesq

variable {F E V}

namespace HermitianForm

def unitaryGroup (h : HermitianForm F E V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb x y := by
    change h.toSesq (a (b x)) (a (b y)) = _
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    change h.toSesq (a.symm x) (a.symm y) = _
    conv_rhs => rw [← a.apply_symm_apply x, ← a.apply_symm_apply y]
    rw [ha]

theorem mem_unitaryGroup {h : HermitianForm F E V} {g : V ≃ₗ[E] V} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y := Iff.rfl

end HermitianForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def gram (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) : Matrix ι ι E :=
  fun i j => B (v i) (v j)

omit [Fintype ι] [DecidableEq ι] in
theorem gram_apply (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) (i j : ι) :
    gram B v i j = B (v i) (v j) := rfl


omit [DecidableEq ι] in
theorem sesq_eq_sum (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V) (x y : V) :
    B x y = ∑ i, ∑ j, conj F E (v.repr x i) * gram B v i j * v.repr y j := by
  conv_lhs => rw [← v.sum_repr x, ← v.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Finset.mul_sum, gram_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
  ring


omit [Fintype ι] [DecidableEq ι] in
theorem isHermitianFor_gram (h : HermitianForm F E V) (v : Basis ι E V) :
    IsHermitianFor (conjHom F E) (gram h.toSesq v) := by
  ext i j
  simp only [transpose_apply, map_apply, gram_apply]
  exact h.isSymm.eq (v j) (v i)

theorem isUnit_det_gram (h : HermitianForm F E V) (v : Basis ι E V) :
    IsUnit (gram h.toSesq v).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← vecMul_surjective_iff_isUnit]
  intro w
  obtain ⟨x, hx⟩ := h.nonsingular.2 (v.constr E w)
  refine ⟨fun i => conj F E (v.repr x i), ?_⟩
  ext j
  have hxj : h.toSesq x (v j) = w j := by rw [hx, Basis.constr_basis]
  rw [← hxj, sesq_eq_sum h.toSesq v]
  simp only [vecMul, dotProduct, Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sesq_apply_map_basis (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (v : Basis ι E V)
    (g : V →ₗ[E] V) (i j : ι) :
    B (g (v i)) (g (v j)) =
      (((LinearMap.toMatrix v v g).map (conjHom F E))ᵀ * gram B v * LinearMap.toMatrix v v g)
        i j := by
  rw [sesq_eq_sum B v]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, LinearMap.toMatrix_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem mem_unitaryGroup_iff_toMatrix (h : HermitianForm F E V) (v : Basis ι E V)
    (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔
      ((LinearMap.toMatrix v v (g : V →ₗ[E] V)).map (conjHom F E))ᵀ * gram h.toSesq v *
        LinearMap.toMatrix v v (g : V →ₗ[E] V) = gram h.toSesq v := by
  constructor
  · intro hg
    ext i j
    rw [← sesq_apply_map_basis]
    exact hg _ _
  · intro hM x y
    have key : (h.toSesq.comp (g : V →ₗ[E] V)).compl₂ (g : V →ₗ[E] V) = h.toSesq := by
      refine LinearMap.ext_basis v v fun i j => ?_
      have := congrFun (congrFun hM i) j
      rw [← sesq_apply_map_basis] at this
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      simpa [gram_apply] using this
    exact LinearMap.congr_fun₂ key x y

noncomputable def autEquivGL (v : Basis ι E V) : (V ≃ₗ[E] V) ≃* GL ι E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv v).toRingEquiv.toMulEquiv)

theorem autEquivGL_apply (v : Basis ι E V) (g : V ≃ₗ[E] V) :
    (autEquivGL v g : Matrix ι ι E) = LinearMap.toMatrix v v (g : V →ₗ[E] V) := by
  simp [autEquivGL]
  rfl

noncomputable def unitaryGroupEquivMatrix (h : HermitianForm F E V) (v : Basis ι E V) :
    h.unitaryGroup ≃* unitaryGroupMatrix (conjHom F E) (gram h.toSesq v) where
  toFun g := ⟨autEquivGL v g, by
    rw [mem_unitaryGroupMatrix, autEquivGL_apply]
    exact (mem_unitaryGroup_iff_toMatrix h v g).1 g.2⟩
  invFun m := ⟨(autEquivGL v).symm m, by
    rw [mem_unitaryGroup_iff_toMatrix h v, ← autEquivGL_apply, MulEquiv.apply_symm_apply]
    exact m.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv m := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change autEquivGL v ((a : V ≃ₗ[E] V) * b) = autEquivGL v a * autEquivGL v b
    exact map_mul _ _ _)

theorem unitaryGroupEquivMatrix_apply (h : HermitianForm F E V) (v : Basis ι E V)
    (g : h.unitaryGroup) :
    ((unitaryGroupEquivMatrix h v g : GL ι E) : Matrix ι ι E) =
      LinearMap.toMatrix v v ((g : V ≃ₗ[E] V) : V →ₗ[E] V) :=
  autEquivGL_apply v g

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HilbertSchmidtCompact
section
namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]


omit [CompleteSpace H] [CompleteSpace K] in
theorem isCompactOperator_innerSL_smulRight (e : H) (y : K) :
    IsCompactOperator ((innerSL 𝕜 e).smulRight y) := by
  refine ⟨(fun c : 𝕜 => c • y) '' Metric.closedBall 0 ‖e‖,
    (isCompact_closedBall 0 ‖e‖).image (continuous_id.smul continuous_const), ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) one_pos) fun x hx => ?_
  refine ⟨⟪e, x⟫_𝕜, ?_, by simp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Metric.mem_ball, dist_zero_right] at hx
  calc ‖⟪e, x⟫_𝕜‖ ≤ ‖e‖ * ‖x‖ := norm_inner_le_norm e x
    _ ≤ ‖e‖ * 1 := by gcongr
    _ = ‖e‖ := mul_one _

def hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (F : Finset ι) :
    H →L[𝕜] K :=
  ∑ i ∈ F, (innerSL 𝕜 (b i)).smulRight (T (b i))

omit [CompleteSpace H] [CompleteSpace K] in
theorem isCompactOperator_hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)
    (F : Finset ι) : IsCompactOperator (hsTruncation b T F) := by
  classical
  unfold hsTruncation
  induction F using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert a F haF ih =>
    rw [Finset.sum_insert haF, FunLike.coe_add]
    exact (isCompactOperator_innerSL_smulRight _ _).add ih

omit [CompleteSpace H] [CompleteSpace K] in
theorem sub_hsTruncation_apply_basis {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι 𝕜 H)
    (T : H →L[𝕜] K) (F : Finset ι) (j : ι) :
    (T - hsTruncation b T F) (b j) = if j ∈ F then 0 else T (b j) := by
  have hb : ∀ i, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := fun i =>
    orthonormal_iff_ite.mp b.orthonormal i j
  simp only [sub_apply, hsTruncation, FunLike.coe_sum, Finset.sum_apply, smulRight_apply,
    innerSL_apply_apply, hb, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
  split_ifs <;> simp


omit [CompleteSpace K] in
theorem hsNormSq_sub_hsTruncation (T : H →L[𝕜] K) (F : Finset (exists_hilbertBasis 𝕜 H).choose) :
    hsNormSq (T - hsTruncation (stdHilbertBasis (𝕜 := 𝕜) (H := H)) T F) =
      ∑' i : {i // i ∉ F}, ‖T (stdHilbertBasis (𝕜 := 𝕜) (H := H) i)‖ₑ ^ 2 := by
  classical
  rw [hsNormSq]
  refine Eq.trans ?_ (tsum_subtype {i | i ∉ F}
    (fun i => ‖T (stdHilbertBasis (𝕜 := 𝕜) (H := H) i)‖ₑ ^ 2)).symm
  refine tsum_congr fun j => ?_
  rw [sub_hsTruncation_apply_basis]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp [hj]

theorem IsHilbertSchmidt.isCompactOperator {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  set b := stdHilbertBasis (𝕜 := 𝕜) (H := H)
  have htail : Tendsto (fun F : Finset (exists_hilbertBasis 𝕜 H).choose =>
      hsNormSq (T - hsTruncation b T F)) atTop (𝓝 0) := by
    simp only [b, hsNormSq_sub_hsTruncation]
    exact ENNReal.tendsto_tsum_compl_atTop_zero hT.ne
  have hHS : ∀ F, IsHilbertSchmidt (T - hsTruncation b T F) := fun F => by
    refine lt_of_le_of_lt ?_ hT
    rw [hsNormSq_sub_hsTruncation, hsNormSq]
    exact tsum_comp_le_tsum_of_injective Subtype.val_injective (fun i => ‖T (b i)‖ₑ ^ 2)
  have hnorm : Tendsto (fun F => hsNorm (T - hsTruncation b T F)) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    simpa [hsNorm, Function.comp_def] using h2
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun F => hsTruncation b T F) ?_
    (Eventually.of_forall fun F => isCompactOperator_hsTruncation b T F)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) hnorm
  rw [norm_sub_rev]
  exact norm_le_hsNorm (hHS F)

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HilbertSchmidtKernel
section
namespace GroundTheory.Automorphic.L2Kernel

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

section SlopeTestRemainingChoices

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    (g : α → E) : eLpNorm' g 2 μ ^ 2 = ∫⁻ a, ‖g a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_two]

theorem lt_top_of_sq_lt_top {a : ℝ≥0∞} (h : a ^ 2 < ∞) : a < ∞ := by
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_pow two_ne_zero] at h
  exact lt_irrefl _ h

end SlopeTestRemainingChoices

variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]

section Kernel

variable (k : Lp 𝕜 2 (μ.prod ν))

end Kernel

end

end GroundTheory.Automorphic.L2Kernel
end

