module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedGenerators
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem BoundedGenerators.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : BoundedGenerators.Statement h v := by
  intro M D t ht
  obtain ⟨c, hc⟩ := hA D
  obtain ⟨d, κ, hκ⟩ := hT M
  obtain ⟨C, hC⟩ := hR d t (|κ| * c) ht
  refine ⟨d, C, fun La g hLa hmin => ?_⟩
  obtain ⟨_, _, hcov⟩ := hc La hLa
  obtain ⟨T, hTn, hTc⟩ := hκ g

  let Φ : W →+ EuclideanSpace ℝ (Fin d) :=
    ((T : (InfinitePlace E → ι → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin d)) : _ →ₗ[ℝ] _).toAddMonoidHom.comp
      (vecAtHom v)
  have hΦ : ∀ x, Φ x = T (vecAt v x) := fun x => rfl
  have hvec : Function.Injective (vecAt v) := by
    intro x y hxy
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    apply v.repr.injective
    ext i
    exact w.embedding.injective (congrFun (congrFun hxy w) i)
  have hΦinj : Function.Injective Φ := T.injective.comp hvec
  let L := ZLattice.comap ℝ (archLattice v La) T.symm.toLinearMap
  have hmemL : ∀ z, z ∈ L ↔ ∃ x ∈ La, Φ x = z := by
    intro z
    rw [← SetLike.mem_coe, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe, mem_archLattice]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [hΦ]
    constructor
    · intro hx; rw [hx]; simp
    · intro hx; rw [← hx]; simp
  have hLmin : ∀ z ∈ L, z ≠ 0 → t ≤ ‖z‖ := by
    intro z hz hz0
    obtain ⟨x, hx, rfl⟩ := (hmemL z).1 hz
    have hx0 : x ≠ 0 := by rintro rfl; exact hz0 (map_zero Φ)
    rw [hΦ, hTn]
    exact hmin x hx hx0
  have hLcov : ZLattice.covolume L ≤ |κ| * c := by
    rw [hTc]
    have h0 : 0 ≤ ZLattice.covolume (archLattice v La) := ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_right (le_abs_self κ) h0).trans
      (mul_le_mul_of_nonneg_left hcov (abs_nonneg κ))
  obtain ⟨b, hb⟩ := hC L hLmin hLcov
  choose e he heb using fun i => (hmemL (b i)).1 (b i).2
  refine ⟨e, le_antisymm ((AddSubgroup.closure_le La).2 (Set.range_subset_iff.2 he)) ?_,
    fun i => ?_⟩
  · intro x hx
    have hxL : Φ x ∈ L := (hmemL _).2 ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨Φ x, hxL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨Φ x, hxL⟩
    have hx' : x = ∑ i, r i • e i := by
      apply hΦinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, heb i]
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [← hTn, ← hΦ, heb i]
    exact hb i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace BoundedInverseCompact

section SlopeTestRemainingChoices

variable {ι : Type*} [Fintype ι]

theorem posDef_exists_lower {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → ℂ, c * ‖y‖ ^ 2 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := by
  set f : (ι → ℂ) → ℝ := fun y => (star y ⬝ᵥ (P *ᵥ y)).re with hf
  have hscale : ∀ (r : ℝ) (y : ι → ℂ), f (r • y) = r ^ 2 * f y := by
    intro r y
    simp only [hf, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
      Complex.smul_re]
    ring
  have hunit : ∀ y : ι → ℂ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  have hrecover : ∀ y : ι → ℂ, y ≠ 0 → f y = ‖y‖ ^ 2 * f (‖y‖⁻¹ • y) := by
    intro y hy
    rw [hscale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_pow,
      one_mul]
  by_cases hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty
  · have hcont : Continuous f := by simp only [hf]; fun_prop
    obtain ⟨y0, hy0, hmin⟩ :=
      (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
    have hy0ne : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    refine ⟨f y0, by simpa [hf] using hP.re_dotProduct_pos hy0ne, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp [hf]
    · change f y0 * ‖y‖ ^ 2 ≤ f y
      rw [hrecover y hy, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hunit y hy)) (sq_nonneg _)
  · refine ⟨1, one_pos, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp
    · exact absurd ⟨_, hunit y hy⟩ hne


omit [Fintype ι] in
theorem norm_mul_apply_le {m κ : Type*} [Fintype κ] (A : Matrix m κ ℂ) (B : Matrix κ ι ℂ)
    (i : m) (j : ι) : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

end SlopeTestRemainingChoices

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [_root_.NumberField.IsTotallyComplex E] [Fintype ι] in
theorem exists_rightInv (v : Basis ι E W) {n : ℕ} {e : Fin n → W}
    (he : Submodule.span E (Set.range e) = ⊤) :
    ∃ c : ι → Fin n → E, ∀ w : InfinitePlace E,
      (Matrix.of fun k a => vecAt v (e a) w k) * (Matrix.of fun a i => w.embedding (c i a)) = 1 := by
  have hmem : ∀ i, ∃ c : Fin n → E, ∑ a, c a • e a = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun E).mp (he ▸ Submodule.mem_top)
  choose c hc using hmem
  refine ⟨c, fun w => ?_⟩
  ext k i
  have h1 : ∑ a, v.repr (e a) k * c i a = v.repr (v i) k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc i, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, of_apply, vecAt, ← map_mul, ← map_sum, h1, Basis.repr_self, one_apply]
  by_cases hki : k = i
  · subst hki
    simp
  · simp [hki]

end BoundedInverseCompact

open BoundedInverseCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem BoundedInverseCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    BoundedInverseCompact.Statement h v := by
  intro M n e he C
  obtain ⟨c, hc⟩ := exists_rightInv v he
  choose κ hκ hκle using fun w => posDef_exists_lower (M.posDef w)
  set U : InfinitePlace E → Matrix ι (Fin n) ℂ := fun w => Matrix.of fun k a => vecAt v (e a) w k
  set R : InfinitePlace E → Matrix (Fin n) ι ℂ := fun w => Matrix.of fun a i => w.embedding (c i a)
  set H := gramAt h v
  set D : InfinitePlace E → ℝ := fun w => 1 + C ^ 2 / κ w
  set r1 : InfinitePlace E → ι → ι → ℝ := fun w _ i => ∑ a, D w * ‖R w a i‖
  set r2 : InfinitePlace E → ι → ι → ℝ :=
    fun w j i => ∑ l, (∑ k, ‖(H w)⁻¹ j k‖ * r1 w l k) * ‖H w l i‖

  have hBx : ∀ r : ι → ι → ℝ, IsCompact {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} := by
    intro r
    have : {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} =
        Set.pi Set.univ fun i => Set.pi Set.univ fun j => Metric.closedBall (0 : ℂ) (r i j) := by
      ext A
      constructor
      · intro hA i _ j _
        simpa using hA i j
      · intro hA i j
        simpa using hA i (Set.mem_univ _) j (Set.mem_univ _)
    rw [this]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  set K : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ({A | ∀ i j, ‖A i j‖ ≤ r2 w i j} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r1 w i j}))
  have hK : ∀ w, IsCompact (K w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hBx _).prod (MulOpposite.opHomeomorph.isCompact_preimage.mp (hBx _)))
  set S := {g : archUnitary h v | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  have hclosed : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_le ?_ continuous_const
    have hw : ∀ w, Continuous fun x : archUnitary h v =>
        (((x⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) := fun w =>
      Units.continuous_val.comp ((continuous_apply w).comp (continuous_subtype_val.comp continuous_inv))
    have hm : ∀ w, Continuous fun x : archUnitary h v => invApply x (vecAt v (e a)) w := fun w =>
      (hw w).matrix_mulVec continuous_const
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
      ((continuous_star.comp (hm w)).dotProduct (continuous_const.matrix_mulVec (hm w))))
  rw [Subtype.isCompact_iff]
  refine (isCompact_univ_pi hK).of_isClosed_subset
    ((isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _ hclosed) ?_
  rintro _ ⟨g, hg, rfl⟩ w -
  set Gi : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set G : Matrix ι ι ℂ := (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

  have hy : ∀ a, ‖invApply g (vecAt v (e a)) w‖ ≤ D w := by
    intro a
    set y := invApply g (vecAt v (e a))
    have hnn : ∀ w', 0 ≤ (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re := fun w' =>
      (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (y w'))).1
    have h0 := Finset.sum_nonneg fun w' (_ : w' ∈ Finset.univ) => hnn w'
    have hsum : ∑ w', (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re ≤ C ^ 2 := by
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hg a) 2
    have hterm := (Finset.single_le_sum (fun w' _ => hnn w') (Finset.mem_univ w)).trans hsum
    have hk := hκle w (y w)
    have hq : ‖y w‖ ^ 2 ≤ C ^ 2 / κ w := by
      rw [le_div_iff₀ (hκ w)]
      nlinarith
    simp only [D]
    nlinarith [norm_nonneg (y w)]

  have hGiU : ∀ j a, (Gi * U w) j a = invApply g (vecAt v (e a)) w j := by
    intro j a
    simp [Gi, U, invApply, Matrix.mul_apply, mulVec, dotProduct]
  have hGi_eq : Gi = Gi * U w * R w := by
    rw [Matrix.mul_assoc, hc w, Matrix.mul_one]
  have hGi_le : ∀ j i, ‖Gi j i‖ ≤ r1 w j i := by
    intro j i
    rw [hGi_eq]
    refine (norm_mul_apply_le _ _ j i).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [hGiU]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ j).trans (hy a)) (norm_nonneg _)

  have hHdet : IsUnit (H w).det := by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  have hinv : Giᴴ * H w * Gi = H w := (mem_archUnitary.mp (g⁻¹).2) w
  have hGiG : Gi * G = 1 := by
    simp only [Gi, G, Subgroup.coe_inv, Pi.inv_apply]
    exact Units.inv_mul _
  have hG_eq : G = (H w)⁻¹ * Giᴴ * H w := by
    have h1 : Giᴴ * H w = H w * G := by
      calc Giᴴ * H w = Giᴴ * H w * (Gi * G) := by rw [hGiG, Matrix.mul_one]
        _ = H w * G := by rw [← Matrix.mul_assoc, hinv]
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHdet, Matrix.one_mul]
  have hG_le : ∀ j i, ‖G j i‖ ≤ r2 w j i := by
    intro j i
    rw [hG_eq]
    refine (norm_mul_apply_le _ _ j i).trans
      (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_apply_le _ _ j l).trans
      (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [conjTranspose_apply, norm_star]
    exact hGi_le l k
  exact ⟨hG_le, hGi_le⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementForm
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace ComplementForm

theorem conj_apply (h : HermitianForm F E W) (x y : W) :
    conjHom F E (h.toSesq x y) = h.toSesq y x :=
  LinearMap.isSymm_def.1 h.isSymm x y

theorem apply_w_v {h : HermitianForm F E W} {v w : W} (hp : IsHyperbolicPair h v w) :
    h.toSesq w v = 1 := by
  rw [← conj_apply h v w, hp.2.2, map_one]

def proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict (hypComplement h v w)
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w) fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, smul_eq_mul, hp.1, hp.2.1, hp.2.2, apply_w_v hp]
      constructor <;> ring

theorem proj_apply (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    (proj h v w hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem eq_add_proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    x = h.toSesq w x • v + (proj h v w hp x : W) + h.toSesq v x • w := by
  rw [proj_apply]; abel

theorem proj_of_mem (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w)
    (x : hypComplement h v w) : proj h v w hp x = x := by
  obtain ⟨h1, h2⟩ := mem_hypComplement.1 x.2
  ext
  rw [proj_apply, h1, h2, zero_smul, zero_smul, sub_zero, sub_zero]

def restr (h : HermitianForm F E W) (v w : W) :
    hypComplement h v w →ₛₗ[conjHom F E] hypComplement h v w →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E) (fun x y => h.toSesq x y)
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul])
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _)])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply])

theorem restr_apply (h : HermitianForm F E W) (v w : W) (x y : hypComplement h v w) :
    restr h v w x y = h.toSesq x y := rfl

def form (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    HermitianForm F E (hypComplement h v w) where
  toSesq := restr h v w
  isSymm := LinearMap.isSymm_def.2 fun x y => conj_apply h x y
  nonsingular := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨h1, h2⟩ := mem_hypComplement.1 a.2
      have hav : h.toSesq a v = 0 := by rw [← conj_apply, h1, map_zero]
      have haw : h.toSesq a w = 0 := by rw [← conj_apply, h2, map_zero]
      have hall : h.toSesq (a : W) = 0 := by
        ext y
        have hy : h.toSesq (a : W) (proj h v w hp y) = 0 := by
          rw [← restr_apply, ha, LinearMap.zero_apply]
        rw [eq_add_proj h v w hp y, map_add (f := _), map_add (f := _), map_smul, map_smul, hav, haw, hy,
          LinearMap.zero_apply]
        simp
      have : (a : W) = 0 := h.nonsingular.1 (hall.trans (map_zero _).symm)
      exact Subtype.ext this
    · intro φ
      obtain ⟨y, hy⟩ := h.nonsingular.2 (φ ∘ₗ proj h v w hp)
      have hpv : proj h v w hp v = 0 := by
        ext; rw [proj_apply, hp.1, apply_w_v hp, one_smul, zero_smul]; simp
      have hpw : proj h v w hp w = 0 := by
        ext; rw [proj_apply, hp.2.1, hp.2.2, one_smul, zero_smul]; simp
      have hyv : h.toSesq y v = 0 := by
        rw [hy, LinearMap.comp_apply, hpv, map_zero]
      have hyw : h.toSesq y w = 0 := by
        rw [hy, LinearMap.comp_apply, hpw, map_zero]
      have hmem : y ∈ hypComplement h v w := by
        rw [mem_hypComplement, ← conj_apply h y v, ← conj_apply h y w, hyv, hyw, map_zero]
        exact ⟨rfl, rfl⟩
      refine ⟨⟨y, hmem⟩, ?_⟩
      ext z
      rw [restr_apply, hy, LinearMap.comp_apply, proj_of_mem]

end ComplementForm

theorem ComplementForm.proof (h : HermitianForm F E W) : ComplementForm.Statement h :=
  fun v w hp => ⟨ComplementForm.form h v w hp, fun _ _ => rfl⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceUnitsFiniteIndex
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem CongruenceUnitsFiniteIndex.proof (E : Type*) [Field E] [NumberField E] :
    CongruenceUnitsFiniteIndex.Statement E := by
  intro N hN
  have hI : Ideal.span {(N : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ :=
    Finite.of_injective _ Units.val_injective
  have : (congruenceUnits E N).FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.FiniteIndex.index_ne_zero

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding

noncomputable section

variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

def mixedSpaceEquivPiOfTotallyComplex [_root_.NumberField.IsTotallyComplex E] :
    mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ) where
  toFun p w := p.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun g := (0, fun w => g w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ rfl
    funext w
    exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
  right_inv _ := rfl

def embeddingBasisOfTotallyComplex [_root_.NumberField.IsTotallyComplex E] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ) :=
  (latticeBasis E).map (mixedSpaceEquivPiOfTotallyComplex E)

theorem embeddingBasisOfTotallyComplex_apply [_root_.NumberField.IsTotallyComplex E]
    (j : Free.ChooseBasisIndex ℤ (𝓞 E)) (w : InfinitePlace E) :
    embeddingBasisOfTotallyComplex E j w = w.embedding (integralBasis E j) := by
  rw [embeddingBasisOfTotallyComplex, Basis.map_apply, latticeBasis_apply]
  exact mixedEmbedding_apply_isComplex _ _ ⟨w, IsTotallyComplex.isComplex w⟩

def piSwapEquiv : (ι → InfinitePlace E → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ι → ℂ) :=
  { Equiv.piComm (fun (_ : ι) (_ : InfinitePlace E) => ℂ) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem CoordEmbedBasis.proof [_root_.NumberField.IsTotallyComplex E] : CoordEmbedBasis.Statement E ι := by
  classical
  let B := (Pi.basis fun _ : ι => embeddingBasisOfTotallyComplex E).map (piSwapEquiv E ι)
  have hB : ∀ k, B k = coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) := by
    rintro ⟨i, j⟩
    funext w i'
    simp only [B, Basis.map_apply, Pi.basis_apply, coordEmbed_apply]
    show (Pi.single i (embeddingBasisOfTotallyComplex E j) : ι → InfinitePlace E → ℂ) i' w = _
    by_cases h : i' = i
    · subst h
      simp [embeddingBasisOfTotallyComplex_apply]
    · simp [Pi.single_eq_of_ne h]
  refine ⟨?_, ?_⟩
  · have hli := B.linearIndependent
    rwa [show (⇑B) = fun k => coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) from
      funext hB] at hli
  · rw [finrank_eq_card_basis B, finrank_eq_card_basis (Pi.basis fun _ : ι => integralBasis E)]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

