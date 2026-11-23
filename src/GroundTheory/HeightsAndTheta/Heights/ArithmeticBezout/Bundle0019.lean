module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

private theorem mem_incIdeal_iff {P : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ u ∈ incidence P k, aeval u g = 0 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

private theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

private theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

private theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

theorem ChowFormReduced.proof_of_prime_separate (hPrime : IncIdealPrime.Statement) (hSep : IncIdealSeparate.Statement) :
    ChowFormReduced.Statement := by
  classical
  intro F _ n k J h hJh hJr hch
  have hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W :=
    fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW
  have hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J :=
    fun W hW => (mem_support_fundCycle_iff hJr).mp hW

  have hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k := by
    intro g
    rw [← hch.2 g]
    constructor
    · intro hg W hW
      exact mem_incIdeal_iff.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)
    · intro hg u hu
      obtain ⟨W, hW, huW⟩ := exists_relComps_of_mem_incidence hu
      exact mem_incIdeal_iff.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW

  have hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support,
      incIdeal W' k ≤ incIdeal W k → W' = W := by
    intro W hW W' hW' hle
    have hne : incIdeal W' k ≠ ⊥ := fun hb => hch.1 (by
      have := (hspan h).mp dvd_rfl W' hW'
      rwa [hb, Ideal.mem_bot] at this)
    have hWW' : W' ≤ W := hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle
    exact le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')

  have hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q} := by
    intro W hW
    have hPW : (incIdeal W k).IsPrime := hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant
    have hhW : h ∈ incIdeal W k := (hspan h).mp dvd_rfl W hW
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hch.1
    have hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k := by
      rwa [← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit] at hhW
    obtain ⟨q, hqf, hqW⟩ := (hPW.multiset_prod_mem_iff_exists_mem _).1 hprod
    have hq : Prime q := UniqueFactorizationMonoid.prime_of_factor q hqf
    have hqh : q ∣ h := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
    have hqle : Ideal.span {q} ≤ incIdeal W k := (Ideal.span_singleton_le_iff_mem _).mpr hqW
    refine ⟨q, hq, le_antisymm ?_ hqle⟩
    have hqP : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q} := by
      intro g hg
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hqh ((hspan g).mpr fun W' hW' =>
        Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)
    obtain ⟨W', hW', hle⟩ := hqP.inf_le'.mp hinf
    have hW'W : W' = W := hsep W hW W' hW' (hle.trans hqle)
    rw [← hW'W]
    exact hle
  choose! q hq hqspan using hprin

  have hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h := by
    refine Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_
    · intro W hW W' hW' hne
      refine (hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_
      have hmem : q W' ∈ incIdeal W k := by
        rw [hqspan W hW]
        exact Ideal.mem_span_singleton.mpr hdvd
      refine (hsep W hW W' hW' ?_).symm
      rw [hqspan W' hW']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    · have := (hspan h).mp dvd_rfl W hW
      rw [hqspan W hW] at this
      exact Ideal.mem_span_singleton.mp this
  have hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W := by
    refine (hspan _).mpr fun W hW => ?_
    rw [hqspan W hW]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁ hdvd₂
  obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp
    u.isUnit
  refine ⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩
  · rw [← mem_incIdeal_iff, hqspan W hW, Ideal.mem_span_singleton]
  · rw [Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one],
      ← hu, hur, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeBallFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeBallFinite.proof (hMass : ConeIntegralMass.Statement) : ConeBallFinite.Statement := by
  intro n e h W f hW hf
  obtain ⟨δ, hδ1, hδ⟩ := hf.exists_multiHomog hW
  have hm := hMass n e δ h W f hW hf hδ
  rw [lt_top_iff_ne_top]
  intro hinf
  unfold coneIntegral at hm
  change (∫ y in coneBall h W, (1 : ℝ) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / _ =
    (δ : ℝ) at hm
  rw [setIntegral_const, measureReal_def, hinf, ENNReal.toReal_top, zero_smul, zero_div] at hm
  have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  exact hδ0 hm.symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.continuous_pointOf (h : HermNorm n) : Continuous h.pointOf := by
  unfold HermNorm.pointOf
  exact Continuous.matrix_mulVec continuous_const (continuous_pi fun i => by fun_prop)

theorem HermNorm.pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit h.matᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transpose]; exact h.isUnit_det)
  have hv : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa [HermNorm.pointOf] using hy)
  ext i
  simpa using congrFun hv i

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem CycleAverage.proof (h1 : ConeAverage.Statement) : CycleAverage.Statement := by
  intro n e δ h Z f hd
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  have hW : ∀ W ∈ Z.support,
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) =
          -(δW W * (harmonic (n - 1) : ℝ)) / 2 :=
    fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)
  have hint : ∀ W ∈ Z.support,
      IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) :=
    fun W hm => (hW W hm).1.const_mul _
  unfold cycleIntegral
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]
  have hterm : ∀ W ∈ Z.support,
      (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) =
        (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2) := by
    intro W hm
    rw [integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ) := by
    rw [← hsum]; push_cast; rfl
  rw [hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem IsChowFormCycle.ne_zero {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1

theorem DefectAverage.proof (h1 : MahlerAverageSplit.Statement) (h2 : CycleAverage.Statement) :
    DefectAverage.Statement := by
  intro n e δ h Z f hZ
  obtain ⟨hi1, hm1⟩ := h1 n e δ h f hZ.chow.ne_zero hZ.homog
  obtain ⟨hi2, hm2⟩ := h2 n e δ h Z f hZ
  have hi : IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) := by
    unfold mahlerDefect; exact hi1.sub hi2
  refine ⟨hi, ?_⟩
  have hsub : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) =
      (⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))) -
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) := by
    simp only [setAverage_eq, mahlerDefect]
    rw [integral_sub hi1 hi2, smul_sub]
  rw [hsub, ← hm1, hm2]
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PEvalSpecFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem EvalSpecFirst.proof : EvalSpecFirst.Statement := by
  intro n k f v w
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) =
    eval₂Hom (RingHom.id ℂ) (consGroup v w) f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar, consGroup]
  | succ i => simp [specFirstVar, consGroup]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogAverage
section
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix

namespace GroundTheory.Heights₂.Heights

theorem FsLogAverage.proof (h1 : BallAverageLinear.Statement) (h2 : FsLogPointOf.Statement)
    (h3 : SphereMeanLinearBall.Statement) (h4 : BallVolume.Statement) : FsLogAverage.Statement := by
  intro n h y hy
  set y' : Fin n → ℂ := fun i => y i with hy'def
  have hy' : y' ≠ 0 := by
    intro hz
    apply hy
    ext i
    exact congrFun hz i
  set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ
  have hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v) := by
    funext v
    exact h2 n h v y
  obtain ⟨hint, hle, hmean⟩ := h3 n y' hy'
  have habs : (fun w => |φ w|) = fun w => -φ w := by
    funext w
    exact abs_of_nonpos (hle w)
  have hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2 := by
    rw [(h1 n h (fun w => |φ w|)).2, habs]
    change (⨍ w in ballH (HermNorm.std n), (-φ) w) = _
    rw [average_neg, hmean]
    ring
  obtain ⟨_, hfin⟩ := h4 n h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]
    exact (h1 n h φ).1.mpr hint
  · simp only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]
    rw [← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]
    ring
  · rw [hrw, (h1 n h φ).2]
    exact hmean

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine Measurable.of_eval fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogPointOf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem FsLogPointOf.proof : FsLogPointOf.Statement := by
  intro n h v y
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hd : h.dualNorm (h.pointOf y) = (HermNorm.std n).dualNorm (fun i => y i) := by
    simp only [HermNorm.dualNorm, HermNorm.pointOf, HermNorm.std, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.transpose_one, inv_one]
  have hn : (HermNorm.std n).norm (h.mat *ᵥ v) = h.norm v := by
    simp only [HermNorm.norm, HermNorm.std, Matrix.one_mulVec]
  have hs : ∑ j, v j * h.pointOf y j = ∑ i, (h.mat *ᵥ v) i * y i := by
    have := Matrix.dotProduct_mulVec v h.matᵀ (fun i => y i)
    rw [Matrix.vecMul_transpose] at this
    simpa [dotProduct, HermNorm.pointOf] using this
  unfold fsLog nrmv
  rw [hd, hn]
  simp only [mul_assoc, ← Finset.mul_sum, hs]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem HermNorm.dualNorm_smul {n : ℕ} (h : HermNorm n) (t : ℂ) (y : Fin n → ℂ) :
    h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by
  unfold HermNorm.dualNorm
  rw [Matrix.mulVec_smul]
  have hs : (∑ i, ‖(t • ((h.mat)ᵀ⁻¹ *ᵥ y)) i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, ‖((h.mat)ᵀ⁻¹ *ᵥ y) i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstSwapMahler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem specFirst_C_mul {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]

end

end GroundTheory.Heights₂.Heights
end

