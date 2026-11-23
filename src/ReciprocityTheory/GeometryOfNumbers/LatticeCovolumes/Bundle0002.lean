module

public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.DegStA
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder Matrix

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem IsFrame.ds_spanK_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span K (Set.range v) = Submodule.span K (E : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  · exact Submodule.span_le.mpr hv.2.2

theorem IsFrame.length_eq_latticeRank {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  unfold latRank
  rw [← hv.ds_spanK_eq, finrank_span_eq_card hv.2.1, Fintype.card_fin]

theorem exists_isFullRankFamily_of_fg (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ r, ∃ v : Fin r → V, IsFrame K E v := by
  obtain ⟨S, hS⟩ := hE
  obtain ⟨b, hbE, hspan, hli⟩ := exists_linearIndependent K (E : Set V)
  have hEle : ∀ x ∈ E, x ∈ Submodule.span K (S : Set V) := by
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ (S : Set V) ?_
    rintro _ ⟨x, rfl⟩
    exact hEle _ (hbE x.2)
  let _ := Fintype.ofFinite b
  refine ⟨Fintype.card b, fun i => ((Fintype.equivFin b).symm i : V), ?_, ?_, ?_⟩
  · intro i; exact hbE ((Fintype.equivFin b).symm i).2
  · exact hli.comp _ (Fintype.equivFin b).symm.injective
  · intro x hx
    have : x ∈ Submodule.span K (b : Set V) := hspan ▸ Submodule.subset_span hx
    have hr : Set.range (fun i => ((Fintype.equivFin b).symm i : V)) = b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin b).symm i).2
      · intro hy; exact ⟨Fintype.equivFin b ⟨y, hy⟩, by simp⟩
    rw [SetLike.mem_coe, hr]
    exact this

theorem IsFrame.relIndex_span_frame_ne_zero {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  set H := S.toAddSubgroup.addSubgroupOf E.toAddSubgroup with hH
  have : Module.Finite (𝓞 K) E := Module.Finite.iff_fg.mpr hE
  have : Module.Finite ℤ E := Module.Finite.trans (𝓞 K) E
  have hfg : AddGroup.FG E := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hfg' : AddGroup.FG E.toAddSubgroup := hfg
  have : Module.Finite ℤ E.toAddSubgroup := Module.Finite.iff_addGroup_fg.mpr hfg'
  have : Module.Finite ℤ (E.toAddSubgroup ⧸ H) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' H).toIntLinearMap
      (QuotientAddGroup.mk'_surjective H)
  have : Finite (E.toAddSubgroup ⧸ H) := by
    apply Module.finite_of_fg_torsion
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hv.2.2 x.2)
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
      have hd : ∀ i, IsIntegral ℤ (y • c i) := fun i => hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i))
      let d : Fin r → 𝓞 K := fun i => ⟨y • c i, hd i⟩
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      have hmem : (y • (x : V)) ∈ S := by
        have : y • (x : V) = ∑ i, d i • v i := by
          rw [← hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← algebraMap_smul K (d i) (v i), ← smul_assoc]
          rfl
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      show (y : ℤ) • (QuotientAddGroup.mk x : E.toAddSubgroup ⧸ H) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hmem
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.ds_form_zero_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have := h.add_right σ x 0 0
  rw [add_zero] at this
  linear_combination -this

theorem HermFam.ds_form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.ds_form_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]

theorem HermFam.ds_form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm, h.ds_form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => h.conj_symm σ y (f i)

theorem HermFam.ds_form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.ds_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    h.gram σ (fun j => ∑ i, G i j • v i) = (G.map σ)ᴴ * h.gram σ v * G.map σ := by
  ext a b
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, h.ds_form_sum_left, h.ds_form_sum_right, h.ds_form_smul_left, h.smul_right,
    Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem HermFam.ds_gram_det_re_pos (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) : 0 < (h.gram σ v).det.re := by
  have := (h.posDef σ r v hv).det_pos
  exact (Complex.pos_iff.mp this).1

theorem HermFam.ds_gram_comb_det_re (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Complex.normSq (σ G.det) * (h.gram σ v).det.re := by
  rw [h.ds_gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, RingHom.map_det]
  have : star (σ.mapMatrix G).det * (h.gram σ v).det * (σ.mapMatrix G).det =
      (Complex.normSq (σ.mapMatrix G).det : ℂ) * (h.gram σ v).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
  rw [RingHom.mapMatrix_apply] at this ⊢
  rw [this, Complex.re_ofReal_mul]

theorem HermFam.ds_log_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (G : Matrix (Fin r) (Fin r) K) (hG : G.det ≠ 0) :
    Real.log (h.gram σ (fun j => ∑ i, G i j • v i)).det.re =
      Real.log (Complex.normSq (σ G.det)) + Real.log (h.gram σ v).det.re := by
  rw [h.ds_gram_comb_det_re, Real.log_mul]
  · exact (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hG)).ne'
  · exact (h.ds_gram_det_re_pos σ hv).ne'

end

section
variable {K : Type*} [Field K] [NumberField K]

theorem ds_prod_embeddings_eq_norm (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom_apply])

theorem ds_sum_log_normSq_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)).ne'),
    ← map_prod, ds_prod_embeddings_eq_norm]
  have hn : (Algebra.norm ℚ x : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hn hn,
    Real.log_abs]
  ring

end

end ReciprocityTheory.GeometryOfNumbersTheory
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re

noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j

private lemma exists_factor_C {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, G = Bᴴ * B := by
  first
  | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
  | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
  | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
  | (refine ⟨hG.posSemidef.sqrt, ?_⟩
     rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
  | (refine ⟨CFC.sqrt G, ?_⟩
     have h0 : 0 ≤ G := hG.posSemidef.nonneg
     have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
     rw [hs, CFC.sqrt_mul_sqrt_self G h0])

private lemma exists_factor_R {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᵀ * B := by
  have hC : ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᴴ * B := by
    first
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
    | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
    | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
    | (refine ⟨hG.posSemidef.sqrt, ?_⟩
       rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
    | (refine ⟨CFC.sqrt G, ?_⟩
       have h0 : 0 ≤ G := hG.posSemidef.nonneg
       have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
       rw [hs, CFC.sqrt_mul_sqrt_self G h0])
  obtain ⟨B, hB⟩ := hC
  exact ⟨B, by rw [hB, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]

private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]

private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]
  skip

private lemma detC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) :
    (Bᴴ * B).det = (Complex.normSq B.det : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl

private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    Convex ℝ (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℂ) r R) ((Matrix.toLin' B).restrictScalars ℝ)

private theorem neg_mem_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    ∀ y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R,
      -y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℂ) r R _ hy

private theorem measurableSet_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    MeasurableSet (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hc : Continuous ((Matrix.toLin' B).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma hermitianEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : G = Bᴴ * B) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  rw [setC_eq]
  exact ⟨convex_preimage_sqBall_complex B R, neg_mem_preimage_sqBall_complex B R, isBounded_preimage_sqBall_complex_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_complex B R⟩

theorem ellipsoidC_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_C hG
  exact hermitianEllipsoid_props_of_eq hG B hB R

private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

private theorem convex_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    Convex ℝ ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℝ) r R) (Matrix.toLin' B)

private theorem neg_mem_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    ∀ y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R, -y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℝ) r R _ hy

private theorem measurableSet_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    MeasurableSet ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet

private lemma realEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : G = Bᵀ * B) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [setR_eq]
  exact ⟨convex_preimage_sqBall_real B R, neg_mem_preimage_sqBall_real B R, isBounded_preimage_sqBall_real_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_real B R⟩

theorem ellipsoidR_props {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_R hG
  exact realEllipsoid_props_of_eq hG B hB R

end ReciprocityTheory.GeometryOfNumbersTheory
end

-- bundled from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadZSt
section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix
open scoped ComplexOrder

theorem neg_log_det_le {r' r : ℕ} (hr : r' ≤ r) {G' : Matrix (Fin r') (Fin r') ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG' : G'.PosDef) (hG : G.PosDef)
    (M : Matrix (Fin r) (Fin r') ℤ) (hM : Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec)
    (N : Matrix (Fin r) (Fin r) ℤ) (hN : N.det ≠ 0) {A lam : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hnorm : (((A : ℂ) ^ 2) • G' -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * G * M.map (Int.cast : ℤ → ℂ)).PosSemidef)
    (hsmall : ∀ i, (((N.map (Int.cast : ℤ → ℂ))ᴴ * G * N.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2) :
    -(1 / 2) * Real.log G'.det.re ≤
      -(1 / 2) * Real.log G.det.re + r' * Real.log A + ((r : ℝ) - r') * Real.log lam := by
  classical
  have hu0 : LinearIndependent ℚ (M.map (Int.cast : ℤ → ℚ)).col := Matrix.mulVec_injective_iff.mp hM
  have hNq : (N.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]; exact_mod_cast hN
  have hw : LinearIndependent ℚ (N.map (Int.cast : ℤ → ℚ)).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hNq.isUnit)
  obtain ⟨m, f, hmr, hLI⟩ := LinearIndependentExtension.exists_append_li _ hu0 _ hw
  subst hmr
  set U : Matrix (Fin (r' + m)) (Fin (r' + m)) ℤ :=
    Matrix.of fun i j => Fin.append (fun k => M i k) (fun k => N i (f k)) j with hUdef
  have hUq : (U.map (Int.cast : ℤ → ℚ)).col =
      Fin.append (M.map (Int.cast : ℤ → ℚ)).col ((N.map (Int.cast : ℤ → ℚ)).col ∘ f) := by
    funext j i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · rw [Fin.append_left]; simp [U, Matrix.col]
    · rw [Fin.append_right]; simp [U, Matrix.col]; rfl
  have hUdet : U.det ≠ 0 := by
    rw [← hUq, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, ← Int.cast_det] at hLI
    exact_mod_cast hLI
  set UC := U.map (Int.cast : ℤ → ℂ) with hUC
  set MC := M.map (Int.cast : ℤ → ℂ) with hMC
  set NC := N.map (Int.cast : ℤ → ℂ) with hNC
  have hUCdet : UC.det = ((U.det : ℤ) : ℂ) := by rw [hUC, Int.cast_det]
  have hUCinj : Function.Injective UC.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hUCdet, isUnit_iff_ne_zero]
    exact_mod_cast hUdet
  set H := UCᴴ * G * UC with hH
  have hHpd : H.PosDef := hG.conjTranspose_mul_mul_same hUCinj
  have hUl : ∀ l i, UC l (Fin.castAdd m i) = MC l i := by intro l i; simp [UC, U, MC]
  have hUr : ∀ l j, UC l (Fin.natAdd r' j) = NC l (f j) := by intro l j; simp [UC, U, NC]
  have hsub : H.submatrix (Fin.castAdd m) (Fin.castAdd m) = MCᴴ * G * MC := by
    ext i j; simp only [H, submatrix_apply, Matrix.mul_apply, conjTranspose_apply, hUl]
  have hdiag : ∀ j, H (Fin.natAdd r' j) (Fin.natAdd r' j) = (NCᴴ * G * NC) (f j) (f j) := by
    intro j; simp only [H, Matrix.mul_apply, conjTranspose_apply, hUr]
  have hMMpd : (MCᴴ * G * MC).PosDef := by
    rw [← hsub]; exact hHpd.submatrix (Fin.castAdd_injective r' m)

  have hdetH : H.det.re = ((U.det : ℝ) ^ 2) * G.det.re := by
    rw [hH, det_mul, det_mul, det_conjTranspose, hUCdet]
    simp [Complex.mul_re, Complex.mul_im, sq]
    ring
  have hd1 : (1 : ℝ) ≤ (U.det : ℝ) ^ 2 := by
    have h1 := Int.one_le_abs hUdet
    have : (1 : ℤ) ≤ U.det ^ 2 := by nlinarith [sq_abs U.det]
    exact_mod_cast this
  have hGpos := (posDef_det_re_pos hG).1
  have hG'pos := (posDef_det_re_pos hG').1
  have hstep1 : G.det.re ≤ H.det.re := by rw [hdetH]; nlinarith
  have hstep2 := det_re_le_mul_prod_diag hHpd
  rw [hsub] at hstep2
  have hprod : ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re ≤ (lam ^ 2) ^ m := by
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le) (fun j _ => ?_)
    rw [hdiag]; exact hsmall _
  have hMM : (MCᴴ * G * MC).det.re ≤ (A ^ 2) ^ r' * G'.det.re := by
    have := det_re_le_of_sub_posSemidef hMMpd hnorm
    rw [det_smul, Fintype.card_fin] at this
    have e : ((A : ℂ) ^ 2) ^ r' = (((A ^ 2) ^ r' : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.re_ofReal_mul] at this
  have hMMpos := (posDef_det_re_pos hMMpd).1
  have hfin : G.det.re ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m := by
    have hP0 : 0 ≤ ∏ j : Fin m, (H (Fin.natAdd r' j) (Fin.natAdd r' j)).re :=
      Finset.prod_nonneg fun j _ => (Complex.pos_iff.mp (hHpd.diag_pos)).1.le
    calc G.det.re ≤ H.det.re := hstep1
      _ ≤ _ := hstep2
      _ ≤ (A ^ 2) ^ r' * G'.det.re * (lam ^ 2) ^ m :=
        mul_le_mul hMM hprod hP0 (by positivity)
  have hlog := Real.log_le_log hGpos hfin
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end ReciprocityTheory.GeometryOfNumbersTheory
end

