module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.SqInt

variable {p q n : ℕ}

def reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Matrix a a ℂ →* Matrix b b ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom

theorem reixHom_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b)
    (g : Matrix a a ℂ) : reixHom e g = Matrix.reindex e e g := rfl

theorem continuous_reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Continuous (reixHom e) :=
  continuous_id.matrix_reindex e e

def covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) : T.G →* Formalism.REAL.UJ ε :=
  ((Units.map (reixHom e)).comp T.cov).codRestrict (Formalism.REAL.UJ ε) fun x => h.cov_mem T x

theorem umat_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    umat (covU h T x) = Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := rfl

theorem continuous_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Continuous (covU h T) :=
  Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp (continuous_fst.comp T.emb.continuous)) _

theorem surjective_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Function.Surjective (covU h T) := by
  intro g
  obtain ⟨x, hx⟩ := h.cov_surj T (g := umat g) g.2
  exact ⟨x, Subtype.ext (Units.ext hx)⟩

theorem isClosedEmbedding_emb (T : GrpData p q) :
    Topology.IsClosedEmbedding (fun x : T.G => (T.cov x, T.sq x)) := by
  refine ⟨T.emb, ?_⟩
  have : Set.range (fun x : T.G => (T.cov x, T.sq x)) =
      {z : GL (Ix p q) ℂ × ℂˣ | (z.1 : Mat p q)ᴴ * Jm p q * z.1 = Jm p q} ∩
        {z | (z.2 : ℂ) ^ 2 = (z.1 : Mat p q).det} := by
    ext ⟨g, w⟩
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact ⟨T.cov_mem x, T.sq_sq x⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx, -⟩ := T.bij g h1 w h2
      exact ⟨x, Prod.ext hx.1 hx.2⟩
  rw [this]
  have c1 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.1 : Mat p q) := Units.continuous_val.comp continuous_fst
  have c2 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.2 : ℂ) := Units.continuous_val.comp continuous_snd
  exact (isClosed_eq ((c1.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul c1) continuous_const).inter
    (isClosed_eq (c2.pow 2) c1.matrix_det)

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖(T.sq x : ℂ)‖ = 1 := by
  have h1 := (mem_Upq _).1 (T.cov_mem x)
  have hJ : (Jm p q).det ≠ 0 := by
    have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
      rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
    rw [Matrix.det_reindex_self] at this
    exact left_ne_zero_of_mul_eq_one this
  have h2 := congrArg (fun A => ‖Matrix.det A‖) h1
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, ← T.sq_sq x, norm_pow] at h2
  have h3 : ‖(T.sq x : ℂ)‖ ^ 4 = 1 := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.2 hJ)
    rw [one_mul]
    conv_rhs => rw [← h2]
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3

theorem isProperMap_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    IsProperMap (covU h T) := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_covU h T, fun K hK => ?_⟩
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hK' : IsCompact ((fun g : Formalism.REAL.UJ ε => (Units.map (reixHom e.symm) g.1 : GL (Ix p q) ℂ)) '' K) :=
    hK.image (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val)
  refine ((isClosedEmbedding_emb T).isCompact_preimage (hK'.prod hS)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_covU h T)) fun x hx => ⟨⟨covU h T x, hx, Units.ext ?_⟩, ?_⟩
  · change Matrix.reindex e.symm e.symm (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q)) = _
    simp
  · simpa using norm_sq_eq_one h T x

theorem isHaarMeasure_map_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    (T.haar.map (covU h T)).IsHaarMeasure :=
  Measure.isHaarMeasure_map T.haar (covU h T) (continuous_covU h T) (surjective_covU h T)
    (isProperMap_iff_tendsto_cocompact.1 (isProperMap_covU h T)).2

theorem isSqIntOn_of_factors : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsSqIntOn ε σ := by
  intro p q n e ε T R σ h hF v w
  have hc : coefOn (ε := ε) σ v w ∘ covU h T = fun g => inner ℂ w (R.U.π g v) := by
    funext x
    simp only [Function.comp, coefOn, umat_covU, hF x]
  have hc1 : Continuous fun g => (inner ℂ w (R.U.π g v) : ℂ) := continuous_const.inner (R.U.cont v)
  have hq := (isProperMap_covU h T).isClosedMap.isQuotientMap (continuous_covU h T) (surjective_covU h T)
  have hc2 : Continuous (coefOn (ε := ε) σ v w) := hq.continuous_iff.2 (hc ▸ hc1)
  haveI := isHaarMeasure_map_covU h T
  rw [Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (T.haar.map (covU h T))]
  refine MemLp.smul_measure ?_ ENNReal.coe_ne_top
  rw [memLp_map_measure_iff hc2.aestronglyMeasurable (continuous_covU h T).measurable.aemeasurable, hc,
    memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable]
  exact (R.schur v w).1

end GlobalTheory.RealPar.SqInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitary
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.CoverURep

variable {p q n : ℕ}

theorem gl_isEmbedding_val :
    Topology.IsEmbedding (Units.val : (Mat p q)ˣ → Mat p q) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Mat p q => A⁻¹) (fun A hA => ?_) (fun u => ?_)
  · have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    exact (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt
  · simp

theorem inducing_pair (T : GrpData p q) (e : Ix p q ≃ Fin n) :
    Topology.IsInducing (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) := by
  have h1 : Topology.IsInducing (fun A : Mat p q => Matrix.reindex e e A) := by
    refine Topology.IsInducing.of_comp (g := fun B : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm B)
      (continuous_id.matrix_reindex e e) (continuous_id.matrix_reindex e.symm e.symm) ?_
    convert Topology.IsInducing.id using 1
    funext A i j
    simp [Matrix.reindex_apply]
  exact ((h1.comp gl_isEmbedding_val.isInducing).prodMap Units.isEmbedding_val₀.isInducing).comp T.emb.isInducing

theorem det_Jm_ne_zero {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) : (Jm p q).det ≠ 0 := by
  have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
    rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  rw [Matrix.det_reindex_self] at this
  exact left_ne_zero_of_mul_eq_one this

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖((T.sq x : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg Matrix.det ((mem_Upq _).1 (T.cov_mem x))
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← T.sq_sq x] at h1
  have h2 := congrArg norm h1
  rw [norm_mul, norm_mul, norm_star, norm_pow] at h2
  have h3 : ‖(Jm p q).det‖ ≠ 0 := norm_ne_zero_iff.2 (det_Jm_ne_zero h)
  have h4 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4

theorem continuousOn_of_cover {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {Y : Type*} [TopologicalSpace Y] (f : Matrix (Fin n) (Fin n) ℂ → Y)
    (hf : Continuous fun x : T.G => f (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))) :
    ContinuousOn f (UJset ε) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  obtain ⟨C, hC, hCe⟩ := (inducing_pair T e).isClosed_iff.1 (ht.preimage hf)
  have hK : CompactSpace (Metric.closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hD : IsClosed {z : Matrix (Fin n) (Fin n) ℂ × Metric.closedBall (0 : ℂ) 1 |
      (z.1, (z.2 : ℂ)) ∈ C ∧ (z.2 : ℂ) ^ 2 = z.1.det} := by
    refine IsClosed.inter (hC.preimage (by fun_prop)) (isClosed_eq (by fun_prop) ?_)
    exact continuous_fst.matrix_det
  refine ⟨_, isClosedMap_fst_of_compactSpace _ hD, ?_⟩
  ext g
  constructor
  · rintro ⟨hg, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, rfl⟩ := h.cov_surj T hU
    have hx : x ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      rw [hCe]; exact hg
    refine ⟨(_, ⟨((T.sq x : ℂˣ) : ℂ), by simp [norm_sq_eq_one h T x]⟩), ⟨hx, ?_⟩, rfl⟩
    simp only [Matrix.det_reindex_self]
    exact T.sq_sq x
  · rintro ⟨⟨⟨g', w, hw⟩, ⟨h1, h2⟩, rfl⟩, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, hx⟩ := h.cov_surj T hU
    simp only at hx h1 h2
    subst hx
    rw [Matrix.det_reindex_self] at h2
    have hw0 : w ≠ 0 := by
      rintro rfl
      have := T.sq_sq x
      rw [← h2] at this
      simp at this
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := T.bij (T.cov x) (T.cov_mem x) (Units.mk0 w hw0) h2
    have hy : y ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      simp only [Set.mem_preimage, hy1, hy2]
      exact h1
    rw [hCe] at hy
    simp only [Set.mem_preimage, hy1] at hy
    exact hy

theorem urep_irred : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ →
      IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ := by
  intro p q n e ε T R σ h hF
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact R.U.isom x v
  · intro v
    refine continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using R.U.cont v
  · intro S hS hst
    refine R.irred S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv

end GlobalTheory.RealPar.CoverURep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Polynomial
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField nonZeroDivisors in
private theorem natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] (k : ℕ) (β : 𝓞 L) (r : 𝓞 K)
    (hβ : β ^ k = algebraMap (𝓞 K) (𝓞 L) r)
    (hgen : Algebra.adjoin K {algebraMap (𝓞 L) L β} = ⊤) :
    (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hint : IsIntegral (𝓞 K) β := Algebra.IsIntegral.isIntegral β
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ k - C r) (by simp [hβ])
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K L β hgen
  have hder : aeval β (derivative (X ^ k - C r : (𝓞 K)[X])) = (k : 𝓞 L) * β ^ (k - 1) := by
    simp [derivative_X_pow]
  rw [← hder, hh, derivative_mul, map_add (f := _), map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  exact Ideal.mul_mem_right _ _ hmem


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField nonZeroDivisors in
theorem _root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (k : ℕ) (hk : 0 < k) (y : K) (hy : y ≠ 0) (I : Submodule (𝓞 K) K)
    (hI : I ^ k = Submodule.span (𝓞 K) {y}) (z : L) (hz : z ^ k = algebraMap K L y)
    (hL : Algebra.adjoin K {z} = ⊤) : (k : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hy' : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr hy
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hy' hz.symm
  have hzk : z ^ k ≠ 0 := pow_ne_zero k hz0
  have htop : K⟮z⟯ = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]
    exact IntermediateField.algebra_adjoin_le_adjoin K {z}
  have hpow : ∀ b ∈ I, ∃ r : 𝓞 K, b ^ k = algebraMap (𝓞 K) K r * y := by
    intro b hb
    have hbk : b ^ k ∈ Submodule.span (𝓞 K) {y} := by
      rw [← hI]
      exact Submodule.pow_mem_pow I hb k
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hbk
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  have hquot : ∀ b ∈ I, ∃ β : 𝓞 L, algebraMap (𝓞 L) L β * z = algebraMap K L b := by
    intro b hb
    obtain ⟨r, hr⟩ := hpow b hb
    have hint : IsIntegral ℤ (algebraMap K L b / z) := by
      refine IsIntegral.of_pow hk ?_
      have hq : (algebraMap K L b / z) ^ k = algebraMap K L (algebraMap (𝓞 K) K r) := by
        rw [div_pow, ← map_pow, hr, map_mul, hz, mul_div_cancel_right₀ _ hy']
      rw [hq]
      exact (RingOfIntegers.isIntegral_coe r).algebraMap
    exact ⟨⟨_, hint⟩, div_mul_cancel₀ _ hz0⟩
  set S : Set (𝓞 L) :=
    {β | ∃ b ∈ I, b ≠ 0 ∧ algebraMap (𝓞 L) L β * z = algebraMap K L b} with hS
  have hmemS : ∀ β ∈ S, (k : 𝓞 L) * β ^ (k - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    rintro β ⟨b, hb, hb0, hβb⟩
    obtain ⟨r, hr⟩ := hpow b hb
    have hβ0 : algebraMap (𝓞 L) L β ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hβb
      exact hb0 ((map_eq_zero _).mp hβb.symm)
    refine natCast_mul_pow_pred_mem_differentIdeal_of_pow_eq k β r ?_ ?_
    · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_pow, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L]
      refine mul_right_cancel₀ hzk ?_
      rw [← mul_pow, hβb, ← map_pow, hr, map_mul, hz]
    · have hK : K⟮algebraMap (𝓞 L) L β⟯ = ⊤ := by
        rw [eq_top_iff, ← htop, IntermediateField.adjoin_simple_le_iff]
        have hzeq : z = algebraMap K L b / algebraMap (𝓞 L) L β := by
          rw [← hβb, mul_div_cancel_left₀ _ hβ0]
        rw [hzeq]
        exact div_mem (IntermediateField.algebraMap_mem _ b)
          (IntermediateField.mem_adjoin_simple_self K _)
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic _), hK, IntermediateField.top_toSubalgebra]
  have key : ∀ n : ℕ, ∀ w ∈ I ^ n, ∃ t ∈ Ideal.span S ^ n,
      algebraMap (𝓞 L) L t * z ^ n = algebraMap K L w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [pow_zero, Submodule.mem_one] at hw
      obtain ⟨r, rfl⟩ := hw
      refine ⟨algebraMap (𝓞 K) (𝓞 L) r, by simp, ?_⟩
      rw [pow_zero, mul_one, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    | succ n ih =>
      intro w hw
      rw [pow_succ] at hw
      refine Submodule.mul_induction_on (C := fun w => ∃ t ∈ Ideal.span S ^ (n + 1),
        algebraMap (𝓞 L) L t * z ^ (n + 1) = algebraMap K L w) hw ?_ ?_
      · intro a ha b hb
        obtain ⟨t, ht, hta⟩ := ih a ha
        by_cases hb0 : b = 0
        · exact ⟨0, zero_mem _, by simp [hb0]⟩
        obtain ⟨β, hβ⟩ := hquot b hb
        refine ⟨t * β, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul ht (Ideal.subset_span ⟨b, hb, hb0, hβ⟩)
        · rw [map_mul, map_mul, pow_succ, ← hta, ← hβ]
          ring
      · rintro x x' ⟨t, ht, htx⟩ ⟨t', ht', htx'⟩
        exact ⟨t + t', add_mem ht ht', by rw [map_add (f := _), add_mul, htx, htx', map_add (f := _)]⟩
  have hspan : Ideal.span S = ⊤ := by
    have hyk : y ∈ I ^ k := by
      rw [hI]
      exact Submodule.mem_span_singleton_self y
    obtain ⟨t, ht, htz⟩ := key k y hyk
    have ht1 : t = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_one]
      refine mul_right_cancel₀ hzk ?_
      rw [htz, hz, one_mul]
    rw [Ideal.eq_top_iff_one]
    exact Ideal.pow_le_self hk.ne' (by rw [← ht1]; exact ht)
  have h1 : (1 : 𝓞 L) ∈ Ideal.span ((fun x => x ^ (k - 1)) '' S) := by
    rw [Ideal.span_pow_eq_top S hspan]
    exact Submodule.mem_top
  have hfin := Submodule.span_induction
    (p := fun x _ => (k : 𝓞 L) * x ∈ differentIdeal (𝓞 K) (𝓞 L))
    (by rintro _ ⟨β, hβ, rfl⟩; exact hmemS β hβ) (by simp)
    (fun x x' _ _ hx hx' => by rw [mul_add]; exact add_mem hx hx')
    (fun a x _ hx => by rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ a hx) h1
  simpa using hfin


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField nonZeroDivisors in
theorem _root_.GlobalTheory.FieldSize.sz_sup_adjoin_root : ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ) (k : ℕ) (y : F) (I : Submodule (𝓞 F) F) (z : ℂ), _root_.GlobalTheory.FieldSize.Sz F a b → 0 < k → y ≠ 0 → I ^ k = Submodule.span (𝓞 F) {y} → z ^ k = (y : ℂ) → _root_.GlobalTheory.FieldSize.Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  intro F a b k y I z hF hk hy hI hz
  unfold _root_.GlobalTheory.FieldSize.Sz at hF ⊢
  obtain ⟨hfd, hdeg, hdisc⟩ := hF
  have hyint : IsIntegral ℚ (y : ℂ) := (Algebra.IsIntegral.isIntegral y).map F.val
  have hzint : IsIntegral ℚ z := IsIntegral.of_pow hk (by rw [hz]; exact hyint)
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzint
  haveI hEfd : FiniteDimensional ℚ ↥(F ⊔ ℚ⟮z⟯) := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  set E := F ⊔ ℚ⟮z⟯ with hE
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  haveI : NumberField E := { to_charZero := inferInstance, to_finiteDimensional := hEfd }
  have hle : F ≤ E := le_sup_left
  letI : Algebra F E := (IntermediateField.inclusion hle).toAlgebra
  letI : Module.Free F E := Module.Free.of_divisionRing F E
  let z' : E := ⟨z, (le_sup_right : ℚ⟮z⟯ ≤ E) (IntermediateField.mem_adjoin_simple_self ℚ z)⟩
  have hz' : z' ^ k = algebraMap F E y :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hz)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap)
  let φ : E →ₐ[F] ℂ := { E.val with commutes' := fun _ => rfl }
  have hL : Algebra.adjoin F {z'} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : (w : ℂ) ∈ Algebra.adjoin F {z} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzF.isAlgebraic]
      have hwr : (w : ℂ) ∈ (IntermediateField.adjoin F {z}).restrictScalars ℚ := by
        have h := IntermediateField.restrictScalars_adjoin_eq_sup ℚ F {z}
        rw [SetLike.ext_iff] at h
        exact (h _).mpr w.2
      exact hwr
    have hmap : Algebra.adjoin F {z} = (Algebra.adjoin F {z'}).map φ := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [hmap] at hw
    obtain ⟨w', hw', hww⟩ := hw
    have hw'w : w' = w := Subtype.val_injective hww
    exact hw'w ▸ hw'
  have hdiff := _root_.GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy I hI z' hz' hL
  have hroot := _root_.GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal F E k hk hdiff
  have hFE : IntermediateField.adjoin F {z'} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra, eq_top_iff, ← hL]
    exact IntermediateField.algebra_adjoin_le_adjoin F {z'}
  have hz'int : IsIntegral F z' := IsIntegral.of_pow hk (by rw [hz']; exact isIntegral_algebraMap)
  have hdegFE : Module.finrank F E ≤ k := by
    have h1 := IntermediateField.adjoin.finrank hz'int
    rw [hFE, IntermediateField.finrank_top'] at h1
    rw [h1]
    have hp : (X ^ k - C y : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hk y
    calc (minpoly F z').natDegree ≤ (X ^ k - C y : F[X]).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd F z' (by simp [hz'])) hp
      _ = k := natDegree_X_pow_sub_C _
  haveI : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  have hdF : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hdFE : 0 < Module.finrank F E := Module.finrank_pos
  have htower : Module.finrank ℚ E = Module.finrank ℚ F * Module.finrank F E :=
    (Module.finrank_mul_finrank ℚ F E).symm
  refine ⟨hEfd, ?_, ?_⟩
  · rw [htower, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    exact add_le_add hdeg (Real.log_le_log (by positivity) (by exact_mod_cast hdegFE))
  · exact hroot.trans (add_le_add hdisc le_rfl)

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateFieldStatement
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_different_le_different_sup_intermediateField : ∀ (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')], letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra; (differentIdeal ℤ (𝓞 F')).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤ differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  first | exact @GlobalTheory.DiffBaseChange.map_different_le_sup | exact GlobalTheory.DiffBaseChange.map_different_le_sup | (intros; apply GlobalTheory.DiffBaseChange.map_different_le_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixesStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) → {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M := by
  first | exact @GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | exact GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix | (intros; apply GlobalTheory.SplitCriterion.ncard_primes_eq_finrank_of_frob_fix <;> assumption)
end

