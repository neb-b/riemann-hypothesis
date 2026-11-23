module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCover
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod pOf)
open GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix

namespace GlobalTheory.CoshSqInt

variable {p q : ℕ}

theorem pOf_mem_pR (B : Matrix (Fin p) (Fin q) ℂ) : pOf B ∈ pR p q := by
  refine ⟨?_, ?_⟩
  · change (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0
    rw [(pOf_herm B).eq]
    simp [pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp [pOf]

theorem exists_cartan (T : GrpData p q) (g : T.G) :
    ∃ k ∈ T.Kset, g = k * T.expt (pOf (cartanB (T.covU g))) := by
  set B := cartanB (T.covU g) with hB
  refine ⟨g * (T.expt (pOf B))⁻¹, ?_, by simp⟩
  obtain ⟨k₁, -, k₂, -, h⟩ := isCartan_cartanB (T.covU g)
  have h1 : ((T.cov g : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.fromBlocks k₁ 0 0 k₂ * ((T.cov (T.expt (pOf B)) : GL (Ix p q) ℂ) : Mat p q) := by
    rw [T.expt_cov _ (pOf_mem_pR B).1]; exact h
  have h2 : ((T.cov (g * (T.expt (pOf B))⁻¹) : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂ := by
    rw [map_mul, map_inv, Units.val_mul, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  change IsKC _
  rw [h2]
  rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp

theorem decay_sq (n : ℕ) (g : Formalism.BasicNotions.UpqT p q) :
    decay n (pOf (cartanB g)) ^ 2 = coshPow (2 * (n : ℝ)) g := by
  unfold decay coshPow singVal
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (pOf (cartanB g)).toBlocks₁₂ = cartanB g := by simp [pOf]
  rw [this, Real.rpow_neg (Real.cosh_pos _).le, inv_pow, ← pow_mul, mul_comm n 2]
  congr 1
  rw [← Real.rpow_natCast]; push_cast; rfl

theorem memLp_two_of_decay : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n →
    ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f →
    (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  intro hI p q n hn T f C hf hd
  obtain ⟨m, hm⟩ := GlobalTheory.MinfMeasure.exists_isMinf p q
  have hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * (n : ℝ) := by
    have : ((p + q : ℕ) : ℝ) < n := by exact_mod_cast hn
    linarith
  have h1 := hI.1 p q m hm _ hc
  haveI := hm.1
  haveI := GlobalTheory.DetSqrtCover.isHaarMeasure_map_covU T
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul (T.haar.map T.covU) m
  have h2 : Integrable (coshPow (2 * (n : ℝ))) (T.haar.map T.covU) := by
    rw [ht]; exact h1.smul_measure_nnreal
  have h3 : Integrable (coshPow (2 * (n : ℝ)) ∘ T.covU) T.haar :=
    h2.comp_measurable (GlobalTheory.DetSqrtCover.continuous_covU T).measurable
  have hfm : AEStronglyMeasurable f T.haar := hf.measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hfm]
  refine (h3.const_mul (C ^ 2)).mono' (hfm.norm.pow 2) (Filter.Eventually.of_forall fun g => ?_)
  obtain ⟨k, hk, hg⟩ := exists_cartan T g
  have h4 := hd k hk _ (pOf_mem_pR (cartanB (T.covU g)))
  rw [← hg] at h4
  rw [Real.norm_of_nonneg (by positivity), Function.comp_apply, ← decay_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

end GlobalTheory.CoshSqInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

def yAt (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 *
    (lamC g.lam (wpD g.abelian₂ v) / 2 - g.C.s * (lamC g.lam (wpF g.abelian₂ v) - g.C.r) - g.C.t)

theorem norm_natCast_le (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem sm_add {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem sm_sub {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add ha (by rwa [norm_neg])

theorem it_add {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)

theorem it_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem sm_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hb

theorem sm_mul' {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ < 1 := by
  rw [mul_comm]; exact sm_mul hb ha

theorem disc_small (W : WeierstrassCurve ℂ_[p]) (x y : ℂ_[p]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (hx : ‖x‖ ≤ 1) (he : W.toAffine.Equation x y) (hy : ‖2 * y + W.a₁ * x + W.a₃‖ < 1)
    (hx' : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1) : ‖W.Δ‖ < 1 := by
  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨1, x, 0, y⟩
  have hΔ : (C • W).Δ = W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ]; simp [C]
  rw [WeierstrassCurve.Affine.equation_iff] at he
  have e1 : (C • W).a₁ = W.a₁ := by simp [C, WeierstrassCurve.variableChange_a₁]
  have e2 : (C • W).a₂ = W.a₂ + 3 * x := by simp [C, WeierstrassCurve.variableChange_a₂]
  have e3 : (C • W).a₃ = 2 * y + W.a₁ * x + W.a₃ := by
    simp [C, WeierstrassCurve.variableChange_a₃]; ring
  have e4 : (C • W).a₄ = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    simp [C, WeierstrassCurve.variableChange_a₄]; ring
  have e6 : (C • W).a₆ = 0 := by
    simp [C, WeierstrassCurve.variableChange_a₆]; linear_combination -he
  rw [← hΔ]
  have A1 : ‖(C • W).a₁‖ ≤ 1 := e1 ▸ h1
  have A2 : ‖(C • W).a₂‖ ≤ 1 := by
    rw [e2]; exact it_add h2 (it_mul (by simpa using norm_natCast_le (p := p) 3) hx)
  have A3 : ‖(C • W).a₃‖ < 1 := e3 ▸ hy
  have A4 : ‖(C • W).a₄‖ < 1 := e4 ▸ hx'
  set V := C • W
  have n4 : ‖(4 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 4
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have n8 : ‖(8 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 8
  have n27 : ‖(27 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 27
  have n9 : ‖(9 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 9
  have B2 : ‖V.b₂‖ ≤ 1 := by
    rw [WeierstrassCurve.b₂]; exact it_add (by rw [sq]; exact it_mul A1 A1) (it_mul n4 A2)
  have B4 : ‖V.b₄‖ < 1 := by
    rw [WeierstrassCurve.b₄]; exact sm_add (sm_mul n2 A4) (sm_mul A1 A3)
  have B6 : ‖V.b₆‖ < 1 := by
    rw [WeierstrassCurve.b₆, e6, mul_zero, add_zero, sq]; exact sm_mul A3.le A3
  have BetaSesquilinearity : ‖V.b₈‖ < 1 := by
    rw [WeierstrassCurve.b₈, e6]
    simp only [mul_zero, add_zero]
    refine sm_sub (sm_add (sm_sub (by norm_num) (sm_mul (it_mul A1 A3.le) A4))
      (sm_mul A2 (by rw [sq]; exact sm_mul A3.le A3))) (by rw [sq]; exact sm_mul A4.le A4)
  rw [WeierstrassCurve.Δ]
  refine sm_add (sm_sub (sm_sub ?_ (sm_mul n8 (by rw [show V.b₄ ^ 3 = V.b₄ * V.b₄ * V.b₄ by ring]; exact sm_mul (it_mul B4.le B4.le) B4)))
    (sm_mul n27 (by rw [sq]; exact sm_mul B6.le B6))) (sm_mul (it_mul (it_mul n9 B2) B4.le) B6)
  rw [neg_mul]
  rw [norm_neg]; exact sm_mul (by rw [sq]; exact it_mul B2 B2) BetaSesquilinearity

end GlobalTheory.ThetaPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodic
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

theorem norm_lamC_root_mul (lam : Qbar →+* ℂ_[p]) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1)
    (x : ℂ) : ‖lamC lam (ζ * x)‖ = ‖lamC lam x‖ := by
  have hq : ζ ∈ Qbar := by
    refine mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.X_pow_sub_C_ne_zero hn 1, ?_⟩
    simp [hζ]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have h1 : ‖lam ⟨ζ, hq⟩‖ = 1 := by
    have e : (⟨ζ, hq⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using hζ)
    have : ‖lam ⟨ζ, hq⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  by_cases hx : x ∈ Qbar
  · have hzx : ζ * x ∈ Qbar := mul_mem hq hx
    simp only [lamC, dif_pos hx, dif_pos hzx]
    have : (⟨ζ * x, hzx⟩ : Qbar) = ⟨ζ, hq⟩ * ⟨x, hx⟩ := rfl
    rw [this, map_mul, norm_mul, h1, one_mul]
  · have hzx : ζ * x ∉ Qbar := by
      intro h
      apply hx
      have : x = ζ⁻¹ * (ζ * x) := by field_simp
      rw [this]
      exact mul_mem (inv_mem hq) h
    simp only [lamC, dif_neg hx, dif_neg hzx]

theorem cval_norm_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  intro D p _ cc δ g hg t ω ht hω
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hcc, hδ⟩).1
  rw [← hΛ] at hlat
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ hlat
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws g.abelian₂ hlat).1.2.2.2 ω hω t
  obtain ⟨m, hm, hmt⟩ := ht
  set s := sgStar g.abelian₂ with hs
  set A : ℂ := (area g.abelian₂ : ℂ) with hAdef
  have hA : area g.abelian₂ = GlobalTheory.latticeArea L := GlobalTheory.OddTheta.area_eq L g.abelian₂ hL
  have hA0 : A ≠ 0 := by
    rw [hAdef, hA]; exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
  set ψ : ℂ := if ω / 2 ∈ g.abelian₂ then 1 else -1 with hψ
  set E : ℂ := Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) with hE
  have key : U1 g.abelian₂ (t + ω) s 0 = (ψ * E) * U1 g.abelian₂ t s 0 := by
    have h2 : s (t + ω) = ψ * s t * Complex.exp (-(-(Real.pi : ℂ) * t * (starRingEnd ℂ) ω / A -
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A))) := by
      have hlaw' := hlaw
      simp only [U1] at hlaw'
      rw [← hlaw', mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    simp only [U1]
    rw [zero_add, zero_add, h2, show ψ * E * (s t * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / A -
        (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) = ψ * s t * (E * Complex.exp (-(Real.pi : ℂ) * 0 *
        (starRingEnd ℂ) t / A - (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) by ring,
      hE, ← Complex.exp_add, mul_assoc (ψ * s t), ← Complex.exp_add]
    congr 1
    congr 1
    simp only [map_add (f := _)]
    ring
  have hroot : (ψ * E) ^ (2 * m) = 1 := by
    have hψ2 : ψ ^ 2 = 1 := by rw [hψ]; split_ifs <;> norm_num
    have ha' : (m : ℂ) * t ∈ L.lattice := (hL _).1 hmt
    have hω' : ω ∈ L.lattice := (hL _).1 hω
    obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ha' hω'
    have hL0 : (GlobalTheory.latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
    have him : ((m : ℂ) * t * (starRingEnd ℂ) ω).im = k * GlobalTheory.latticeArea L := by
      rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff (GlobalTheory.latticeArea_pos L).ne'] at hk
      exact hk
    have hc : (starRingEnd ℂ) ((m : ℂ) * t * (starRingEnd ℂ) ω) = (m : ℂ) * (starRingEnd ℂ) t * ω := by
      simp [map_mul]
    have hsub := Complex.sub_conj ((m : ℂ) * t * (starRingEnd ℂ) ω)
    rw [hc, him] at hsub
    have hexp : ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A))
          = (Real.pi : ℂ) * ((m : ℂ) * t * (starRingEnd ℂ) ω - (m : ℂ) * (starRingEnd ℂ) t * ω) / A := by
            push_cast; field_simp
        _ = (Real.pi : ℂ) * (((2 * (k * GlobalTheory.latticeArea L) : ℝ) : ℂ) * Complex.I) / A := by rw [hsub]
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [hAdef, hA]; push_cast; field_simp
    rw [mul_pow, pow_mul, hψ2, one_pow, one_mul, hE, ← Complex.exp_nat_mul, hexp,
      Complex.exp_int_mul_two_pi_mul_I]
  unfold cval
  rw [key]
  exact norm_lamC_root_mul g.lam (by omega) hroot _

end GlobalTheory.ThetaTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBou
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

noncomputable section

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) : coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have h : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · have h := (hF.1.contDiff (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = d⁄dX (GL3Theta.ser1 lam F) := by
  ext n
  rw [coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, taylorCoeffAtZero_deriv]
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  rw [ha]
  have e : ((n : ℂ) + 1) * (a (n + 1) : ℂ) = ((((n : Qbar) + 1) * a (n + 1) : Qbar) : ℂ) := by
    push_cast; rfl
  rw [e, GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul, map_add (f := _), map_natCast, map_one,
    mul_comm]

theorem atU_deriv (g : GL3Theta.G1 p) {F : ℂ → ℂ} (hF : AlgEnt F) :
    d⁄dX (g.atU F) =
      g.atU (deriv F) * (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * d⁄dX g.l) := by
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, derivative_subst hs, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem bddSer_derivative {f : PowerSeries ℂ_[p]} (hf : BddSer f) : BddSer (d⁄dX f) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  rw [coeff_derivative, norm_mul]
  have h1 : ‖((n : ℂ_[p]) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  calc _ ≤ B * 1 := mul_le_mul (hB _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    _ = B := mul_one B

end GlobalTheory.ThetaTransl.CubeSer

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem sqThD_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  intro p _ g hOk hL h2 h3 hd hσ v hv hw
  obtain ⟨-, hwi, -, -, hA⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hOk hL h2 h3 hd
  have hq : IsWq g.W g.wq := hOk.2.1
  obtain ⟨hS, hB⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hmul, hconst, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨i1, i2, i3, i4, i6, -⟩ := hOk.1
  obtain ⟨vI, hvI, hvl⟩ := PI.JetsPhW.Inv.inverse_omega_holds p g.W g.wq i1 i2 i3 i4 i6 hq
  rw [PI.JetsPhW.Inv.dX_eq_derivative] at hvl
  change vI * d⁄dX g.l = 1 at hvl
  have hσd := algEnt_deriv hσ
  have hSd := algEnt_deriv hS
  have hm2 : (((-2 : Qbar)) : ℂ) = -2 := by push_cast; rfl
  have hc := hconst (((-2 : Qbar)) : ℂ) (-2 : Qbar).2
  have hl2 : lamC g.lam (((-2 : Qbar)) : ℂ) = -2 := by
    rw [GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  have k1 := (hmul (sgStar g.abelian₂) (deriv (sqTh g.abelian₂ v)) hσ hSd).1
  have k2 := (hmul (deriv (sgStar g.abelian₂)) (sqTh g.abelian₂ v) hσd hS).1
  have k3 := (hmul (fun _ => (((-2 : Qbar)) : ℂ)) (fun z => deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)
    hc.1 k2.1).1
  have k4 := (hmul (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z)
    (fun z => (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) k1.1 k3.1).2
  have hT : sqThD g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z) := by
    funext z
    rw [hm2]
    simp only [sqThD]
    ring
  refine ⟨hT ▸ k4.1, ?_⟩
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  set L := lineSer g.wq⁻¹ (xAt g v) with hL'
  obtain ⟨-, hbdd, hCb, hX, -⟩ := SerRing.series_ring_laws p
  refine ⟨vI * (X * d⁄dX L - 2 * L), ?_, ?_⟩
  · have hX2 : BddSer (X ^ 2 : PowerSeries ℂ_[p]) := by
      rw [pow_two]; exact (hbdd _ _ ⟨1, hX⟩ ⟨1, hX⟩).2.2
    have hLb : BddSer L := by
      rw [hL', lineSer]; exact (hbdd _ _ ⟨1, hwi⟩ (hbdd _ _ (hCb _).1 hX2).2.2).2.1
    have h2b : BddSer (2 : PowerSeries ℂ_[p]) := by
      rw [show (2 : PowerSeries ℂ_[p]) = C 2 from (map_ofNat C 2).symm]; exact (hCb 2).1
    refine (hbdd _ _ ⟨1, fun n => hvI n⟩ (hbdd _ _ ((hbdd _ _ ⟨1, hX⟩ (bddSer_derivative hLb)).2.2)
      ((hbdd _ _ h2b hLb).2.2)).2.1).2.2
  · have dA := atU_deriv g hσ
    have dB := atU_deriv g hS
    rw [hA] at dA
    rw [hB] at dB
    have hDA : d⁄dX (C ε * X * e) = C ε * (e + X * d⁄dX e) := by
      simp only [Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul]
      ring
    have hDB : d⁄dX (e ^ 2 * L) =
        2 * e * d⁄dX e * L + e ^ 2 * d⁄dX L := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hDA] at dA
    rw [hDB] at dB
    have F4 : C ε * C ε⁻¹ = (1 : PowerSeries ℂ_[p]) := by
      rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero _), map_one]
    set a1 := g.atU (deriv (sgStar g.abelian₂))
    set b1 := g.atU (deriv (sqTh g.abelian₂ v))
    set x := C ε
    set y := C ε⁻¹
    set l' := d⁄dX g.l
    set E' := d⁄dX e
    set L'' := d⁄dX L
    have ha1 : a1 = (e + X * E') * vI := by
      linear_combination (-a1) * F4 + (-a1 * x * y) * hvl + (-y * vI) * dA + ((e + X * E') * vI) * F4
    have hb1 : b1 = y * (2 * e * E' * L + e ^ 2 * L'') * vI := by
      linear_combination (-b1) * F4 + (-b1 * x * y) * hvl + (-y * vI) * dB
    have hT' : g.atU (sqThD g.abelian₂ v) = x * X * e * b1 + C (-2) * (a1 * (e ^ 2 * L)) := by
      rw [← hA, ← hB, ← hl2]
      calc g.atU (sqThD g.abelian₂ v) = g.atU (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
            (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) := by rw [← hT]
        _ = _ := by rw [k4.2, k1.2, k3.2, k2.2, hc.2]
    rw [hT', show (C (-2) : PowerSeries ℂ_[p]) = -2 by rw [map_neg, map_ofNat]]
    linear_combination (x * X * e) * hb1 - (2 * e ^ 2 * L) * ha1 +
      (X * e * (2 * e * E' * L + e ^ 2 * L'') * vI) * F4

end GlobalTheory.ThetaTransl.CubeSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanish
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem GlobalTheory.torsion_parallelogram_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  intro Λ _ N hN M h0 _ hlaw t ht
  by_cases hQ : t ∈ Λ
  · exact h0 t hQ
  have key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧
      M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [h0 0 (zero_mem Λ)]
      · simp
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ := by
        have e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t) := by
          rw [nsmul_eq_mul]; push_cast; ring
        rw [e]; exact AddSubgroup.nsmul_mem Λ ht _
      have h := hlaw (((k:ℂ)+1) * t) t hmem ht hQ
      have e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t := by ring
      have e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t := by ring
      rw [e1, e2, ih.1, ih.2] at h
      push_cast
      linear_combination h
  have h1 := (key N).1
  rw [h0 _ ht] at h1
  have hN' : (N:ℝ)^2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1.symm).resolve_left hN'
end

