module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0007
public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemHalfPlane
section
open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def An (TT : ℝ) : Set ℂ := {ζ | TT < Complex.normSq ζ}

theorem isOpen_An (TT : ℝ) : IsOpen (An TT) :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exp_mem_An {w : ℂ} (hw : w ∈ Hh TT) : Complex.exp w ∈ An TT := by
  exact hw

theorem hasFDerivAt_exp_real (w : ℂ) :
    HasFDerivAt Complex.exp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w)) w := by
  have h : HasFDerivAt Complex.exp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp w)).restrictScalars ℝ) w :=
    (Complex.hasDerivAt_exp w).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (bet α)
      (α (Complex.exp w) • (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w) +
        Complex.exp w • (fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w := by
  have he := hasFDerivAt_exp_real w
  have hmem : Complex.exp w ∈ An TT := exp_mem_An hw
  have hdα : DifferentiableAt ℝ α (Complex.exp w) :=
    (hα.contDiffAt ((isOpen_An TT).mem_nhds hmem)).differentiableAt
      (by first | simp | exact le_top)
  have hc : HasFDerivAt (fun z => α (Complex.exp z))
      ((fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w :=
    hdα.hasFDerivAt.comp w he
  exact hc.mul he

theorem fderiv_bet_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (v : ℂ) :
    fderiv ℝ (bet α) w v = (α (Complex.exp w) * Complex.exp w + wZ α (Complex.exp w) * Complex.exp w ^ 2) * v +
      wZb α (Complex.exp w) * Complex.exp w * (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v := by
  rw [(hasFDerivAt_bet hα hw).fderiv]
  unfold wZ wZb
  obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ α (Complex.exp w) := ⟨_, rfl⟩
  rw [← hL]
  have hL' : ∀ u : ℂ, 2 * L u = (u + (starRingEnd ℂ) u) * L 1 + Complex.I * ((starRingEnd ℂ) u - u) * L Complex.I := by
    intro u
    have hre : L u = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
      have hu : u.re • (1 : ℂ) + u.im • Complex.I = u := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      conv_lhs => rw [← hu]
      rw [map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have h1 := Complex.add_conj u
    have h2 := Complex.sub_conj u
    push_cast at h1 h2
    rw [hre]
    linear_combination (-(L 1)) * h1 + (Complex.I * L Complex.I) * h2 +
      (2 * (u.im : ℂ) * L Complex.I) * Complex.I_sq
  have key := hL' (Complex.exp w * v)
  have hcj : (starRingEnd ℂ) (Complex.exp w * v) = (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v :=
    map_mul (starRingEnd ℂ) _ _
  rw [hcj] at key
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  linear_combination (Complex.exp w / 2) * key

theorem sym_alg (A b ζ h k : ℂ) (hb : b.re = 0) :
    ((A * h + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) h) * k).im =
      ((A * k + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) k) * h).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.conj_re,
    Complex.conj_im, hb]
  ring

theorem contDiffOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bet α) (Hh TT) := by
  have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.exp (Hh TT) :=
    Complex.contDiff_exp.contDiffOn
  exact (hα.comp he (fun w hw => exp_mem_An hw)).mul he

theorem contDiffOn_om (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (om α) (Hh TT) :=
  omL.contDiff.comp_contDiffOn (contDiffOn_bet hα)

theorem fderiv_om_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (h k : ℂ) :
    fderiv ℝ (om α) w h k = 2 * (fderiv ℝ (bet α) w h * k).im := by
  have hb := hasFDerivAt_bet hα hw
  have hom : HasFDerivAt (om α) (omL.comp (fderiv ℝ (bet α) w)) w :=
    omL.hasFDerivAt.comp w hb.differentiableAt.hasFDerivAt
  rw [hom.fderiv]
  simp [omL, two_smul, two_mul]

theorem om_sym (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ∀ p ∈ Hh TT, ∀ h k : ℂ, fderiv ℝ (om α) p h k = fderiv ℝ (om α) p k h := by
  intro p hp h k
  rw [fderiv_om_apply hα hp, fderiv_om_apply hα hp, fderiv_bet_apply hα hp, fderiv_bet_apply hα hp,
    sym_alg _ _ _ h k (hcurv _ (exp_mem_An hp))]

def x0 (TT : ℝ) : ℂ := (Real.log (TT + 1) : ℂ)

theorem base_point_mem_half_plane (hTT : 0 ≤ TT) : x0 TT ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT))
  unfold x0
  rw [← Complex.ofReal_exp, Complex.normSq_ofReal, Real.exp_log (by linarith)]
  nlinarith

def th (TT : ℝ) (α : ℂ → ℂ) (w : ℂ) : ℝ := prim (om α) (x0 TT) w

theorem hasFDerivAt_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (th TT α) (om α w) w :=
  hasFDerivAt_prim (isOpen_Hh TT) (convex_Hh TT) (base_point_mem_half_plane hTT) ((contDiffOn_om hα).of_le (by simp))
    (om_sym hα hcurv) hw

theorem contDiffOn_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (Hh TT) := by
  have hHo : IsOpen (Hh TT) :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hHo]
  refine ⟨fun y hy => (hasFDerivAt_th hTT hα hcurv hy).differentiableAt.differentiableWithinAt, ?_⟩
  exact (contDiffOn_om hα).congr (fun y hy => (hasFDerivAt_th hTT hα hcurv hy).fderiv)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Block32EqZeroOfUnipotent
section
namespace Formalism.FourierDecayAlt.P.S3x9

open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

end Formalism.FourierDecayAlt.P.S3x9
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CentreBlockStructure
section
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.S3x8

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3

section Key

variable {A F : Type} [CommRing A] [CommRing F]

end Key

section Corner

variable {A F : Type} [CommRing A] [CommRing F]

end Corner

section Maps

variable {A F : Type} [CommRing A] [CommRing F]

end Maps

section DVR

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

variable [IsDomain o] [IsDiscreteValuationRing o]

end DVR

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk

end Blocks

section Stab

variable {F : Type} [Field F] {r k : ℕ}

end Stab

section Forcing

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}

variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]


end Forcing

end Formalism.FourierDecayAlt.P.S3x8
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CuspidalIrreducibleSubrep
section
open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

noncomputable def geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j ∈ Finset.range n, t ^ (n - 1 - j) • (-X) ^ j

theorem geom {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * geoS X t = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hnil : ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (X ^ k) i j = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply_ne]
      intro h; rw [h] at hij; omega
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < i + k
      · rw [ih i l hl, zero_mul]
      · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]
  have hXn : X ^ n = 0 := by
    ext i j
    have hj := j.isLt
    simp [hnil n i j (by omega)]
  have hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ)) := (Commute.one_right _).smul_right t
  have h := hc.mul_geom_sum₂ n
  have hS : ∑ i ∈ Finset.range n, (-X) ^ i * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - i) = geoS X t := by
    unfold geoS
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, mul_one]
  rw [hS, smul_pow, one_pow, neg_pow, hXn, mul_zero, zero_sub] at h
  have e : t • (1 : Matrix (Fin n) (Fin n) ℂ) + X = -(-X - t • 1) := by rw [neg_sub, sub_neg_eq_add]
  rw [e, neg_mul, h, neg_neg]

theorem det_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := by
  rw [Matrix.det_of_upperTriangular]
  · simp [hX _ _ le_rfl]
  · intro i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp [Matrix.one_apply_ne hne, hX i j hij.le]

theorem sum_eq_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (t : ℂ) :
    ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) = ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold geoS
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) =
      ρ ⬝ᵥ ((∑ j ∈ Finset.range m, t ^ (n - 1 - j) • (-X) ^ j) *ᵥ B) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Matrix.add_mulVec, dotProduct_add,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm (t ^ (n - 1 - k))]
  exact key n

theorem Mcoord_eq {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Mcoord t X B ρ σ = blk (wMat n) 0 0 1 * blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold Mcoord blk
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply]
  · ext i j; simp [Matrix.mul_apply]

theorem det_blk_ne {n : ℕ} (t : ℂ) (ht : t ≠ 0) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have hdet : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := det_shift X hX t
  have ht' : t ^ n ≠ 0 := pow_ne_zero n ht
  have hinv : IsUnit (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det := by rw [hdet]; exact ht'.isUnit
  letI := (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).invertibleOfIsUnitDet hinv
  have hA : ⅟(t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) = (t ^ n)⁻¹ • geoS X t := by
    apply invOf_eq_right_inv
    rw [Matrix.mul_smul, geom X hX t, smul_smul, inv_mul_cancel₀ ht', one_smul]
  rw [Matrix.det_fromBlocks₁₁, hdet, hA, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  field_simp
  try ring

theorem continuous_blk_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Continuous fun t : ℂ => blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by
  unfold blk
  fun_prop

theorem continuous_geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Continuous fun t : ℂ => geoS X t := by
  unfold geoS
  fun_prop

theorem det_blk {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  by_cases ht : t = 0
  swap
  · exact det_blk_ne t ht X hX B ρ σ
  have hc1 : Continuous fun s : ℂ => (blk (s • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det :=
    (continuous_blk_shift X B ρ σ).matrix_det
  have hc2 : Continuous fun s : ℂ => s ^ n * σ - ρ ⬝ᵥ (geoS X s *ᵥ B) :=
    ((continuous_pow n).mul continuous_const).sub
      (continuous_const.dotProduct ((continuous_geoS X).matrix_mulVec continuous_const))
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc1 hc2 (fun s hs => det_blk_ne s hs X hX B ρ σ)
  exact congrFun heq t

theorem det_Mcoord {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (Mcoord t X B ρ σ).det = (wMat n).det *
      (t ^ n * σ - ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j)) := by
  have hW : (blk (wMat n) 0 0 1).det = (wMat n).det := by
    unfold blk
    rw [Matrix.det_reindex_self]
    simp only [Pi.zero_apply]
    rw [show (Matrix.of fun _ _ => (0 : ℂ) : Matrix _ (Fin n) ℂ) = 0 from rfl, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [Mcoord_eq, Matrix.det_mul, det_blk t X hX, sum_eq_geoS, hW]

theorem detMXY : DetMXY := by
  intro m D t p hC
  have hX := isStrictUpper_strictUpper (redOf m p).2.2.1
  have h := det_Mcoord t (strictUpper (redOf m p).2.2.1) hX (redOf m p).2.2.2
    (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1
  rw [cornerSplit m _ _ _ _ t] at h
  have e : detM (MXY m D t p) = (Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
      (Fin.cons (rhoXY m D t p) (redOf m p).2.1) (redOf m p).1).det := rfl
  rw [e, h]
  congr 1
  have hC' : Cof (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 t ≠ 0 := hC
  rw [rhoXY, rho1, mul_div_cancel₀ _ hC']
  ring

theorem redIntegrable : RedIntegrable := by
  intro m β t c ht V _ _ _ Φ hint
  have hemb := embedding_coordMap (m + 1) t ht
  have hJ := jacobian (m + 1) β t ht
  have hfun : blockIntegrand β (m + 1) Φ t c = Fint β m Φ t c ∘ coordMap (m + 1) t :=
    funext (blockIntegrand_eq β m Φ t c ht)
  have hpos : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  set κ : NNReal := Real.toNNReal ((‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (Real.toNNReal_pos.2 (by positivity)).ne'
  have hF : Integrable (Fint β m Φ t c) (muBlock β (m + 1)) := by
    have h : Integrable (Fint β m Φ t c) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) :=
      hemb.integrable_map_iff.2 (hfun ▸ hint)
    rw [hJ, ENNReal.smul_def] at h
    exact (integrable_smul_measure (by simpa using hκ0) ENNReal.coe_ne_top).1 h
  have hmp := mp_consMap β m
  have hG : Integrable (fun q => Fint β m Φ t c (consMap m q)) (muRed β m) :=
    hmp.integrable_comp_of_integrable hF
  have hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      Cof (strictUpper y.2.1) y.2.2 t) := ((continuous_cof m t).comp continuous_snd).measurable
  set α : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t with hα
  set γ : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t with hγ
  have hαm : Measurable α := measurable_const.div hcC
  have hγm : Measurable γ := (measurable_const.sub (continuous_remainder m t).measurable).div hcC
  have hm := affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β
    α γ hαm hγm ((ae_cof_ne' β t ht m).mono fun y hy => div_ne_zero (pow_ne_zero _ ht) hy)
  have hT : Measurable (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m)) := by fun_prop
  have hd : Measurable (fun p : RedCoord m => (‖α p.2‖₊ ^ 2 : NNReal)) := by fun_prop
  have hG' : Integrable (fun q => Fint β m Φ t c (consMap m q))
      (Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal)))) := by
    have : Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = muRed β m := hm
    rw [this]; exact hG
  have h5 := hG'.comp_measurable hT
  have h6 := (integrable_withDensity_iff_integrable_smul hd).1 h5
  have h7 : Integrable (fun q : RedCoord m => ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      redIntegrand β m Φ (c * t ^ (m + 1)) t q) (muRed β m) := by
    refine h6.congr (Filter.Eventually.of_forall fun q => ?_)
    have := pointwise_red β m Φ t c ht q
    simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Function.comp]
    rw [← Complex.coe_smul]
    exact this
  have hne : ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  exact (integrable_smul_iff hne _).1 h7

theorem innerXYOfReduced : InnerXYOfReduced := by
  intro hOm hRI hSplit hAmp m β t c ht V _ _ _ Φ hint
  have hmp := (hSplit m β).2
  have i1 : PolishSpace (XY m) := inferInstance
  have i2 : StandardBorelSpace (XY m) := inferInstance
  have i3 : SecondCountableTopology (RedCoord m) := inferInstance
  have i4 : MeasurableSpace.CountablyGenerated (RedCoord m) := inferInstance
  have i5 : MeasurableSpace.CountablySeparated (RedCoord m) := inferInstance
  have hemb : MeasurableEmbedding (redOf m) := hmp.measurable.measurableEmbedding (hSplit m β).1.injective
  have hfun : (fun p : XY m =>
      psi β (g0 ((-1) ^ (m + 3) * (c * t ^ (m + 1))) p.1 / t) • amp β m Φ (c * t ^ (m + 1)) t p) =
      redIntegrand β m Φ (c * t ^ (m + 1)) t ∘ redOf m :=
    funext fun p => hAmp m β (c * t ^ (m + 1)) t ht V Φ p
  have h1 := hRI m β t c ht V Φ hint
  have h2 := hOm m β t c ht V Φ hint
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hmp.integrable_comp_emb hemb).2 h1
  · rw [h2, hfun]
    exact (hmp.integral_comp hemb _).symm

end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep

namespace Formalism.FourierDecayAlt.P

theorem det_matrix_xy : Formalism.FourierDecayAlt.G.DetMXY := CuspidalIrreducibleSubrep.detMXY

theorem reduced_integrand_integrable : Formalism.FourierDecayAlt.G.RedIntegrable := CuspidalIrreducibleSubrep.redIntegrable

theorem inner_xy_of_reduced : Formalism.FourierDecayAlt.G.InnerXYOfReduced := CuspidalIrreducibleSubrep.innerXYOfReduced

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionOfSteps
section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

theorem germExpansionOfSteps : Formalism.FourierDecayAlt.A6.GermAssemble := by
  intro hHead hPhi K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨L₀, Λ₀, hL₀, hΛ₀, hΦ⟩ := hHead K R ψ hD hn m h Q hQ hQu
  obtain ⟨V, hV, hG⟩ := hPhi K R ψ hD hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQ hQu
  refine ⟨V, hV, fun t c ht hc n' Z' => ?_⟩
  obtain ⟨Φ, hyp, h1, h2⟩ := hΦ n' Z'
  rw [h1 t c, hG Φ hyp t c ht hc]
  congr 1
  funext z
  exact (h2 z).symm

end Formalism.FourierDecayAlt.P
end
end

