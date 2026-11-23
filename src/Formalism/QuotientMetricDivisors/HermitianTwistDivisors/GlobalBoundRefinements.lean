module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0005
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

theorem eKaux (C0 f N La m L e : ℝ) (hC0 : 1 ≤ C0) (hf : 1 ≤ f) (hN : 1 ≤ N)
    (h : e ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) :
    e ≤ C0 * (f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L) := by
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have h0 : 0 ≤ f * N ^ 2 := by positivity
  have h1 : f * N ^ 2 * (La + 1) = f * N ^ 2 * La + f * N ^ 2 := by ring
  linarith

theorem recAux (X B0 Nc m C0 ce Eb lx2 A : ℝ) (hX : 0 < X) (hNc : 0 ≤ Nc)
    (hC0 : 1 ≤ C0) (hce : C0 ≤ ce) (hl : 0 ≤ lx2) (hEb : Eb ≤ ce * m * (X * B0 + lx2 * Nc)) :
    0 ≤ lx2 * Nc / X ∧ X ≤ ce / C0 * X ∧ Eb ≤ C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) ∧
    (50 * C0 + 10) * (A + m * (B0 + lx2 * Nc / X) * (ce / C0 * X)) =
      (50 * C0 + 10) * A + (50 * C0 + 10) * (ce / C0) * (m * (X * B0 + lx2 * Nc)) := by
  have hC : 0 < C0 := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : 1 ≤ ce / C0 := by rw [le_div_iff₀ hC]; linarith
    nlinarith
  · have : C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) = ce * m * (X * B0 + lx2 * Nc) := by
      field_simp
    rw [this]; exact hEb
  · field_simp

theorem constant_factor_le_sixty (C0 ce : ℝ) (hC0 : 1 ≤ C0) (hce : 0 ≤ ce) : (50 * C0 + 10) * (ce / C0) ≤ 60 * ce := by
  have hC : 0 < C0 := by linarith
  rw [mul_div_assoc', div_le_iff₀ hC]
  nlinarith [mul_nonneg hce (sub_nonneg.2 hC0)]

theorem divIneqRecord_of (H : TheoremDivIneq) : DivIneqRecord := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa
    x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce Lpass Eb e6 eP logOm eK pq w eE δ
  intro s1 s2 s3 s4 s5 s6 s7 s8 z1 z2 z3 z4 z5 l1 l2 l3 l4 hB0 hNc c1 c2 c3 c4 r1 r2 r3 r4 r5 hw
    g1 g2 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hC0 hce e1 e2 e3 e4 e5 e6' e7
  have hX : 0 < x ^ eps := Real.rpow_pos_of_pos (by linarith only [z1]) _
  have hb : 0 < b := by rw [z4]; exact Real.exp_pos _
  have hB0' : 0 ≤ B0 := by rw [hB0]; positivity
  obtain ⟨t0, t1, t2, t3⟩ := recAux (x ^ eps) B0 Nc m C0 ce Eb ((Real.log x) ^ 2) ((TT.card : ℝ) * a * La) hX hNc hC0 hce (sq_nonneg _) e2
  have hc : 0 < 50 * C0 + 10 := by linarith only [hC0]
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have p2' : N ^ 2 * 1 ≤ b := by rw [mul_one]; exact p2
  have key := H J Pl TT muC mu0 Fo hu hP mlam logT hK aT phν nν fa
    x eps L b a rd La B0 ((Real.log x) ^ 2 * Nc / x ^ eps) (ce / C0 * x ^ eps) m f k N S tt η w'' b' 1 (m * lam0) C0
    Lpass Eb e6 eP logOm eK pq w eE δ
    s1 s2 s3 s4 s5 s6 s7 s8 z1 z2 z3 z4 z5 l1 l2 l3 l4 hB0 t0 t1 c1 c2 c3 c4 r1 r2 r3 r4 r5 le_rfl hw
    g1 g2 p1 p2' p3 p4 p5 p6 p7 p8 p9 p10 hC00 e1 t2
    (fun j => eKaux C0 f N La m L (eK j) hC0 c4 r2 (e3 j))
    e4 e5 e6' e7
  rw [t3] at key
  have hfac : (50 * C0 + 10) * (ce / C0) ≤ 60 * ce := constant_factor_le_sixty C0 ce hC0 (by linarith only [hC0, hce])
  have hnn : 0 ≤ m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) :=
    mul_nonneg (by linarith only [c3]) (add_nonneg (mul_nonneg hX.le hB0') (mul_nonneg (sq_nonneg _) hNc))
  have hmul := mul_le_mul_of_nonneg_right hfac hnn
  linarith only [key, hmul]

end DivisorInequalityBounds

theorem divisor_inequality_explicit : DivIneqRecord := DivisorInequalityBounds.divIneqRecord_of divisor_inequality

section Rho

open Formalism.DivisionValues.RationalHermitianForm Formalism.DivisionValues.StepBAux Formalism.DivisionValues.ConjugateWeightGram

namespace DivisorInequalityBounds

section LocalW

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end LocalW

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

end Rho

namespace DivisorInequalityBounds

end DivisorInequalityBounds


namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

end Formalism.DivisionValues
