module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HermHalfRight
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace ThetaZeroHermitianLemmas

lemma herm_add_left (L : PeriodPair) (x y w : ℂ) : herm L (x + y) w = herm L x w + herm L y w := by
  simp only [herm]; ring

lemma herm_add_right (L : PeriodPair) (x y w : ℂ) : herm L w (x + y) = herm L w x + herm L w y := by
  simp only [herm, map_add (f := _)]; ring

lemma herm_zero_left (L : PeriodPair) (w : ℂ) : herm L 0 w = 0 := by
  simp [herm]

lemma herm_conj (L : PeriodPair) (x y : ℂ) : herm L x y = conj (herm L y x) := by
  simp only [herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring

lemma herm_sub_swap (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = -(2 * Complex.I * (altE L y x : ℂ)) := by
  rw [herm_conj L x y]
  apply Complex.ext <;> simp [altE]
  all_goals ring

lemma thetaZero_periodLattice_eq (L : PeriodPair) (t z : ℂ) :
    th0 L t z = sgStar L (z + t) * Complex.exp (-(Real.pi : ℂ) * herm L z t) / sgStar L t := by
  have h1 : Complex.exp (-(Real.pi : ℂ) * herm L z t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-(Real.pi : ℂ) * herm L z t) * Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [← Complex.exp_add]; congr 1
  have h2 : Complex.exp (-(Real.pi : ℂ) * herm L 0 t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [herm_zero_left]; congr 1; ring
  simp only [th0, opU, zero_add, h1, h2]
  rw [← mul_assoc, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]

lemma exp_pi_int (k : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (k : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) := by
  have h : Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    ring
  rw [Complex.exp_neg]
  exact inv_eq_of_mul_eq_one_right h

end ThetaZeroHermitianLemmas

open ThetaZeroHermitianLemmas

theorem th0Const_of (hb : SgStarBasic) : ThetaZeroConstant := by
  intro L t
  have h : opU L t (sgStar L) 0 = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) := by
    simp only [opU, zero_add, herm_zero_left]; congr 2; ring
  refine ⟨h, fun ht => ?_⟩
  rw [h]
  exact mul_ne_zero (fun h0 => ht (((hb L).2.2.1 t).1 h0)) (Complex.exp_ne_zero _)

theorem th0Class_of (hb : SgStarBasic) (hq : SgStarQuasi) : ThetaZeroClass := by
  intro L t ω z hω ht
  have hs : sgStar L t ≠ 0 := fun h0 => ht (((hb L).2.2.1 t).1 h0)
  have hc : semiChar L ω ≠ 0 := by unfold semiChar; split_ifs <;> norm_num
  have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * herm L z (t + ω))
      = Complex.exp (-(Real.pi : ℂ) * herm L z t)
        * Complex.exp ((Real.pi : ℂ) * herm L t ω + (Real.pi : ℂ) * herm L ω ω / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    rw [herm_add_left, herm_add_right]; ring
  rw [thetaZero_periodLattice_eq L (t + ω) z, thetaZero_periodLattice_eq L t z, ← add_assoc, hq L ω (z + t) hω, hq L ω t hω,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) hs) hs]
  linear_combination (semiChar L ω * sgStar L (z + t) * sgStar L t) * key

theorem th0Basic_of (hb : SgStarBasic) (hq : SgStarQuasi) (hi : AltEInt) : ThetaZeroBasic := by
  intro L ω₀ hω hn
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn ⊢
  have hs : sgStar L t ≠ 0 := fun h0 => hn (((hb L).2.2.1 t).1 h0)
  have hχ : semiChar L (t + t) = -1 := by
    rw [semiChar, if_neg (by rw [h2]; exact hn)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hd := (hb L).1
    show Differentiable ℂ (fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0)
    simp only [opU, herm]
    fun_prop
  · simp only [th0]
    exact div_self ((th0Const_of hb L t).2 hn)
  · intro z
    rw [thetaZero_periodLattice_eq L t (-z), thetaZero_periodLattice_eq L t z]
    have h1 : sgStar L (-z + t) = -sgStar L (z - t) := by
      rw [show -z + t = -(z - t) by ring]; exact (hb L).2.1 _
    have h3 := hq L (t + t) (z - t) hω
    rw [show z - t + (t + t) = z + t by ring, hχ] at h3
    have key : Complex.exp (-(Real.pi : ℂ) * herm L (-z) t)
        = Complex.exp ((Real.pi : ℂ) * herm L (z - t) (t + t) + (Real.pi : ℂ) * herm L (t + t) (t + t) / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [← Complex.exp_add]; congr 1
      simp only [herm, map_add (f := _), map_neg, map_sub]; ring
    rw [h1, h3]
    linear_combination (-sgStar L (z - t) / sgStar L t) * key
  · intro z
    rw [thetaZero_periodLattice_eq, div_eq_zero_iff, mul_eq_zero, (hb L).2.2.1]
    simp [Complex.exp_ne_zero, hs]
  · intro ω hω' z
    obtain ⟨k, hk⟩ := hi L ω (t + t) hω' hω
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
        = Complex.exp (-((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))) := by
      rw [hk]; push_cast; exact (exp_pi_int k).symm
    have hsw := herm_sub_swap L (t + t) ω
    have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L (z + ω) t)
        = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [he]; simp only [← Complex.exp_add]; congr 1
      simp only [herm, map_add (f := _)] at hsw ⊢
      linear_combination ((Real.pi : ℂ) / 2) * hsw
    rw [thetaZero_periodLattice_eq L t (z + ω), thetaZero_periodLattice_eq L t z, show z + ω + t = (z + t) + ω by ring, hq L ω (z + t) hω']
    linear_combination (semiChar L ω * sgStar L (z + t) / sgStar L t) * key

theorem th0LogDeriv_of (hl : SigmaLogDeriv) (he : EtaSplit) (hzq : ZetaQuasi)
    (hzo : ZetaOdd) : ThetaZeroLogDerivative := by
  intro L ω₀ z hω hn hzt
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn hzt ⊢
  have hζ : wZeta L t = s2 L * t + ((Real.pi : ℂ) / (area L : ℂ)) * conj t := by
    have h1 := hzq L (t + t) (-t) hω (by rwa [neg_mem_iff])
    rw [show -t + (t + t) = t by ring, hzo, he] at h1
    simp only [map_add (f := _)] at h1
    linear_combination h1 / 2
  have hd1 : HasDerivAt (fun w => wSigma L (w + t)) (wZeta L (z + t) * wSigma L (z + t)) z := by
    have := (hl L (z + t) hzt).comp z ((hasDerivAt_id' z).add_const t)
    rw [mul_one] at this
    exact this
  have hg : HasDerivAt (fun w : ℂ => -(s2 L) * (w + t) ^ 2 / 2
        + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2))
      (-(s2 L) * (z + t) - (Real.pi : ℂ) * (conj t / (area L : ℂ))) z := by
    have e1 := ((((hasDerivAt_id' z).add_const t).mul ((hasDerivAt_id' z).add_const t)).const_mul
      (-(s2 L))).div_const 2
    have e2 := (((hasDerivAt_id' z).mul_const (conj t / (area L : ℂ))).const_mul
      (-(Real.pi : ℂ))).sub_const ((Real.pi : ℂ) * herm L t t / 2)
    refine ((e1.add e2).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, herm]; ring
  have hfull := (hd1.mul hg.cexp).div_const (opU L t (sgStar L) 0)
  have hfun : th0 L t = fun w => wSigma L (w + t) * Complex.exp (-(s2 L) * (w + t) ^ 2 / 2
      + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) / opU L t (sgStar L) 0 := by
    funext w
    simp only [th0]
    congr 1
    simp only [opU, sgStar]
    rw [Complex.exp_add]; ring
  rw [hfun]
  refine hfull.congr_deriv ?_
  beta_reduce
  rw [hζ]; ring

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OperatorUComm
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace OperatorUThetaLemmas

lemma conj_herm (L : PeriodPair) (x y : ℂ) : conj (herm L x y) = herm L y x := by
  simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma herm_sub_herm (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = 2 * Complex.I * (altE L x y : ℂ) := by
  rw [← conj_herm L x y, Complex.sub_conj]
  simp only [Formalism.L2.Th1.F.altE]
  push_cast
  ring

lemma herm_add_left (L : PeriodPair) (x y w : ℂ) :
    herm L (x + y) w = herm L x w + herm L y w := by
  simp only [Formalism.L2.Th1.F.herm]
  ring

lemma herm_add_right (L : PeriodPair) (w x y : ℂ) :
    herm L w (x + y) = herm L w x + herm L w y := by
  simp only [Formalism.L2.Th1.F.herm, map_add (f := _)]
  ring

lemma altE_swap (L : PeriodPair) (x y : ℂ) : altE L y x = -altE L x y := by
  simp only [Formalism.L2.Th1.F.altE]
  rw [← conj_herm L x y, Complex.conj_im]

end OperatorUThetaLemmas

open OperatorUThetaLemmas

private theorem mul_exp_mul_exp_eq_exp_mul_of_add_eq (f a b c d : ℂ) (h : a + b = c + d) :
    f * Complex.exp a * Complex.exp b = Complex.exp c * (f * Complex.exp d) := by
  rw [mul_assoc, ← Complex.exp_add, h, Complex.exp_add]
  ring

theorem operator_u_mul : OpUMul := by
  intro L x y F z
  simp only [opU]
  rw [add_assoc z x y]
  apply mul_exp_mul_exp_eq_exp_mul_of_add_eq
  simp only [Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_left, Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_right]
  linear_combination (-(Real.pi : ℂ) / 2) * Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_sub_herm L x y

theorem operator_u_comm : OpUComm := by
  intro L F z
  refine ⟨by simp [opU, herm], fun x y => ?_⟩
  rw [operator_u_mul L x y F z, operator_u_mul L y x F z, add_comm y x,
    Formalism.L2.Th1.F.OperatorUThetaLemmas.altE_swap L x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace PeriodAreaSignLemmas

def det (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

def sgn (L : PeriodPair) : ℤ := if 0 < (L.ω₂ / L.ω₁).im then 1 else -1

lemma det_eq (L : PeriodPair) : det L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp [det, Complex.mul_im]
  ring

lemma det_ne_zero (L : PeriodPair) : det L ≠ 0 := by
  intro h
  rw [det_eq] at h
  have key := LinearIndependent.pair_iff.mp L.indep
  have h1 := key L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext
    · simp; linarith
    · simp; ring)
  have h2 := key L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext
    · simp; ring
    · simp; linarith)
  have h3 : L.ω₁ = 0 := by
    apply Complex.ext
    · simpa using h2.2
    · simpa using h1.2
  have h4 := key 1 0 (by simp [h3])
  exact one_ne_zero h4.1

lemma ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  intro h
  apply det_ne_zero L
  simp [det, h]

lemma div_im (L : PeriodPair) : (L.ω₂ / L.ω₁).im = det L / Complex.normSq L.ω₁ := by
  rw [Complex.div_im, det_eq]; ring

lemma div_im_pos_iff (L : PeriodPair) : 0 < (L.ω₂ / L.ω₁).im ↔ 0 < det L := by
  have hn : 0 < Complex.normSq L.ω₁ := Complex.normSq_pos.mpr (ω₁_ne_zero L)
  rw [div_im, div_pos_iff_of_pos_right hn]

lemma area_eq (L : PeriodPair) : area L = |det L| := rfl

lemma area_pos (L : PeriodPair) : 0 < area L := abs_pos.mpr (det_ne_zero L)

lemma det_eq_sgn_mul (L : PeriodPair) : det L = (sgn L : ℝ) * area L := by
  rw [area_eq, sgn]
  split_ifs with h
  · rw [abs_of_pos ((div_im_pos_iff L).mp h)]; simp
  · have : det L < 0 := lt_of_le_of_ne (not_lt.mp (fun h' => h ((div_im_pos_iff L).mpr h')))
      (det_ne_zero L)
    rw [abs_of_neg this]; simp

lemma sgn_odd (L : PeriodPair) : ¬ Even (sgn L) := by
  rw [sgn]; split_ifs <;> decide

lemma disc_eq (L : PeriodPair) :
    L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ = -(2 * Complex.I * (det L : ℂ)) := by
  rw [det_eq]
  apply Complex.ext
  · simp; ring
  · simp; ring

lemma disc_ne_zero (L : PeriodPair) : L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ ≠ 0 := by
  rw [disc_eq]
  have : (det L : ℂ) ≠ 0 := by exact_mod_cast det_ne_zero L
  simp [this]

lemma exists_coord (L : PeriodPair) (x : ℂ) : ∃ a b : ℝ, x = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
  refine ⟨L.basis.repr x 0, L.basis.repr x 1, ?_⟩
  have := L.basis.sum_repr x
  rw [Fin.sum_univ_two] at this
  simpa using this.symm

lemma wEta_coord (L : PeriodPair) (a b : ℝ) :
    wEta L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = (a : ℂ) * wEta L L.ω₁ + (b : ℂ) * wEta L L.ω₂ := by
  have : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = a • L.ω₁ + b • L.ω₂ := by simp
  rw [this, map_add (f := _), map_smul, map_smul]; simp

end PeriodAreaSignLemmas

open PeriodAreaSignLemmas

theorem areaPos_thm : AreaPos := fun L => area_pos L

theorem etaSplit_of (h : Legendre) : EtaSplit := by
  intro L x
  have hL := h L
  have hs : ((if 0 < (L.ω₂ / L.ω₁).im then 1 else -1 : ℂ)) = ((sgn L : ℤ) : ℂ) := by
    rw [sgn]; split_ifs <;> simp
  rw [hs] at hL
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (area_pos L).ne'
  have hD := disc_ne_zero L
  have hDe := disc_eq L
  have hdet : (det L : ℂ) = ((sgn L : ℤ) : ℂ) * (area L : ℂ) := by
    exact_mod_cast det_eq_sgn_mul L
  set D := L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ with hDdef
  have hpi : ((Real.pi : ℂ) / (area L : ℂ)) * D
      = -(((sgn L : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [hDe, hdet]; field_simp
  have hs2 : s2 L * D = wEta L L.ω₁ * conj L.ω₂ - wEta L L.ω₂ * conj L.ω₁ := by
    rw [s2, ← hDdef]; field_simp
  have e1 : wEta L L.ω₁ = s2 L * L.ω₁ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₁ := by
    apply mul_right_cancel₀ hD
    linear_combination (-L.ω₁) * hs2 - (conj L.ω₁) * hpi - (conj L.ω₁) * hL + wEta L L.ω₁ * hDdef
  have e2 : wEta L L.ω₂ = s2 L * L.ω₂ + ((Real.pi : ℂ) / (area L : ℂ)) * conj L.ω₂ := by
    apply mul_right_cancel₀ hD
    linear_combination (-L.ω₂) * hs2 - (conj L.ω₂) * hpi - (conj L.ω₂) * hL + wEta L L.ω₂ * hDdef
  obtain ⟨a, b, rfl⟩ := exists_coord L x
  rw [wEta_coord]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal]
  linear_combination (a : ℂ) * e1 + (b : ℂ) * e2

namespace PeriodAreaSignLemmas

lemma altE_coord (L : PeriodPair) (m n m' n' : ℤ) :
    altE L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((-(sgn L * (m * n' - n * m')) : ℤ) : ℝ) := by
  have hA : area L ≠ 0 := (area_pos L).ne'
  rw [altE, herm, Complex.div_ofReal_im, div_eq_iff hA]
  have h1 : (((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) * conj ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)).im
      = -((m * n' - n * m' : ℝ) * det L) := by
    rw [det_eq]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [h1, det_eq_sgn_mul]
  push_cast
  ring

lemma semiChar_coord (L : PeriodPair) (m n : ℤ) :
    semiChar L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = if Even m ∧ Even n then 1 else -1 := by
  have key : ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n := by
    constructor
    · intro hx
      obtain ⟨a, b, e⟩ := PeriodPair.mem_lattice.mp hx
      have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - 2 * a) ((n : ℝ) - 2 * b) (by
        simp only [Complex.real_smul]
        push_cast
        linear_combination (-2 : ℂ) * e)
      refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
      · have h1 : (m : ℝ) = 2 * a := by linarith [this.1]
        have : m = 2 * a := by exact_mod_cast h1
        omega
      · have h1 : (n : ℝ) = 2 * b := by linarith [this.2]
        have : n = 2 * b := by exact_mod_cast h1
        omega
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      refine PeriodPair.mem_lattice.mpr ⟨a, b, ?_⟩
      push_cast
      ring
  rw [semiChar]
  simp only [key]

lemma exp_pi_int (k : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)) = if Even k then 1 else -1 := by
  have : (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.mp h).neg_one_zpow

end PeriodAreaSignLemmas

theorem alternating_form_integral : AltEInt := by
  intro L x y hx hy
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.mp hy
  exact ⟨_, altE_coord L m n m' n'⟩

theorem alternating_form_basis : AltEBasis := by
  intro L
  have := altE_coord L 1 0 0 1
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at this
  rw [this, sgn]
  split_ifs <;> simp

theorem semi_character_mul : SemiCharMul := by
  intro L x y hx hy
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.mp hy
  have hadd : (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ + ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((m + m' : ℤ) : ℂ) * L.ω₁ + ((n + n' : ℤ) : ℂ) * L.ω₂ := by
    push_cast; ring
  rw [hadd, semiChar_coord, semiChar_coord, semiChar_coord, altE_coord, exp_pi_int]
  have hsg := sgn_odd L
  by_cases h1 : Even m <;> by_cases h2 : Even n <;> by_cases h3 : Even m' <;>
    by_cases h4 : Even n' <;>
    simp [Int.even_add, Int.even_sub, Int.even_mul, h1, h2, h3, h4, hsg]

end Formalism.L2.Th1.F
end
end

