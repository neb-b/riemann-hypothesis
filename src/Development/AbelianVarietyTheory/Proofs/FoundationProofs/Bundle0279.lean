module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.ArchimedeanLeaf.LeafARCHFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebra
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

namespace GlobalTheory.TranslLin

open PowerSeries

theorem taylorCoeffAtZero_const_mul (F : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coef1 (fun z => c * F z) n = c * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

theorem taylorCoeffAtZero_linearCombination {ι : Type} (s : Finset ι) (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (hφ : ∀ k, Differentiable ℂ (φ k)) (n : ℕ) :
    coef1 (fun z => ∑ k ∈ s, c k * φ k z) n = ∑ k ∈ s, c k * coef1 (φ k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z) := by
      fun_prop
    rw [GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]

theorem exists_retraction : ∃ π : ℂ →ₗ[Qbar] Qbar, ∀ q : Qbar, π (q : ℂ) = q := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))
  exact ⟨π, fun q => LinearMap.congr_fun hπ q⟩

theorem lamC_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {y : ℂ} (h : y ∈ Qbar) :
    lamC lam y = lam ⟨y, h⟩ := dif_pos h

theorem transl_lin : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  intro p _ g ι _ φ c E hE hφ hEq
  obtain ⟨π, hπ⟩ := exists_retraction
  refine ⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩
  have hE' : E = fun z => ∑ k, c k * φ k z := funext hEq
  have key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) =
      ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) := by
    intro n
    have h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n := by
      rw [hE']; exact taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n
    have h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n) :=
      congrArg π h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπ, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hser : GL3Theta.ser1 g.lam E =
      ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n),
      GlobalTheory.SerTransport.lamC_coe]
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  simp only [GlobalTheory.SerTransport.atU_eq, hser]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← coe_substAlgHom hs, map_sum, map_mul]
  simp only [coe_substAlgHom, subst_C]
  rfl

end GlobalTheory.TranslLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshConstNumericalBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem cosh_const_numerical_bound (p q : ℕ) :
    (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) * (2 ^ (2 * (p + q) * min p q) * (2 * Real.pi / (2 / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q)) ≤ Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) := by
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    simp
  have hsq : (p + q) ^ 2 = (p ^ 2 + q ^ 2) + 2 * (p * q) := by ring
  have hmin : 2 * (p + q) * min p q ≤ 4 * (p * q) := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hR : Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2))
      = (((p + q : ℕ) : ℝ) + 2) ^ (3 * (p + q) ^ 2) := by
    have : (3 * ((p + q : ℕ) : ℝ) ^ 2) = ((3 * (p + q) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [hR, hsq]
  have ha : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpos
  generalize ((p + q : ℕ) : ℝ) = a at ha
  generalize p ^ 2 + q ^ 2 = d
  generalize 2 * (p + q) * min p q = m at hmin
  generalize p * q = n at hmin
  have ha0 : 0 < a := by linarith
  have hpi := Real.pi_pos
  have hmax : max 1 (3 / 2 * a ^ 2) = 3 / 2 * a ^ 2 := max_eq_right (by nlinarith)
  have h1 : 18 / 5 * (3 / 2 * a ^ 2) / a = 27 / 5 * a := by field_simp; ring
  have h2 : 2 * Real.pi / (2 / ((a + 1) / 2)) ^ 2 = Real.pi * ((a + 1) ^ 2 / 8) := by
    field_simp; ring
  rw [hmax, h1, h2]
  have h3 : (2 : ℝ) ^ m ≤ 16 ^ n := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (4 * n) := pow_le_pow_right₀ (by norm_num) hmin
      _ = 16 ^ n := by rw [pow_mul]; norm_num
  have h4 : 27 / 5 * a * (9 / 2) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show (0 : ℝ) ≤ a + 8 by linarith)]
  have h5 : 8 * a * (a + 1) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) ha0.le]
  have h6 : (27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8) ≤ (a + 2) ^ 6 := by
    have h7 : (8 * a * (a + 1)) ^ 2 ≤ ((a + 2) ^ 3) ^ 2 := by gcongr
    have h8 : 0 ≤ (a * (a + 1)) ^ 2 := by positivity
    nlinarith
  calc (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (2 ^ m * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n)
      ≤ (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (16 ^ n * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n) := by gcongr
    _ = (27 / 5 * a * (9 / 2)) ^ d * ((27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8)) ^ n := by
        rw [pow_add, pow_mul, mul_pow Real.pi, mul_pow (27 / 5 * a) (9 / 2),
          mul_pow _ ((a + 1) ^ 2 / 8), mul_pow _ (16 : ℝ)]
        field_simp
    _ ≤ ((a + 2) ^ 3) ^ d * ((a + 2) ^ 6) ^ n := by gcongr
    _ = (a + 2) ^ (3 * (d + 2 * n)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

end GlobalTheory.CartanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.DupNorm

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem i_add {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem i_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 :=
  by rw [sub_eq_add_neg]; exact i_add ha (by rwa [norm_neg])

theorem i_mul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem i_pow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem i_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one K (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

theorem i_neg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by rwa [norm_neg]

theorem i_one : ‖(1 : K)‖ ≤ 1 := by simp

theorem b_le (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg

theorem delta_eq (W : WeierstrassCurve K) (x : K) :
    W.Δ = (-48 * x ^ 2 - 8 * W.b₂ * x + (W.b₂ ^ 2 - 32 * W.b₄)) *
        (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) +
      (12 * x ^ 3 - W.b₂ * x ^ 2 - 10 * W.b₄ * x + (W.b₂ * W.b₄ - 27 * W.b₆)) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem max_norm_eq (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) (x : K) :
    max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ =
      max 1 ‖x‖ ^ 4 := by
  obtain ⟨b2, b4, b6, b8⟩ := b_le W h1 h2 h3 h4 h6
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · have hp : ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    have hq : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    rw [max_eq_left hx, one_pow]
    refine le_antisymm (max_le hp hq) ?_
    rw [← hΔ, delta_eq W x]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_) <;> rw [norm_mul] <;>
      refine mul_le_of_le_one_left (norm_nonneg _) ?_ <;> repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
  · have hR1 : 1 ≤ ‖x‖ := hx.le
    have bd : ∀ {c : K}, ‖c‖ ≤ 1 → ∀ {k m : ℕ}, k ≤ m → ‖c * x ^ k‖ ≤ ‖x‖ ^ m := by
      intro c hc k m hkm
      rw [norm_mul, norm_pow]
      calc ‖c‖ * ‖x‖ ^ k ≤ 1 * ‖x‖ ^ m :=
            mul_le_mul hc (pow_le_pow_right₀ hR1 hkm) (by positivity) zero_le_one
        _ = ‖x‖ ^ m := one_mul _
    have hφ : x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ =
        x ^ 4 + -(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0) := by ring
    have hψ : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0 := by ring
    have hr : ‖W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0‖ ≤ ‖x‖ ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (bd b4 le_rfl) (bd (i_mul (i_ofNat 2) b6) (by norm_num)))) (bd b8 (by norm_num)))
    have hs : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0‖ ≤ ‖x‖ ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le (bd (i_ofNat 4) le_rfl) (bd b2 (by norm_num))))
          (bd (i_mul (i_ofNat 2) b4) (by norm_num)))) (bd b6 (by norm_num)))
    have h24 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have h34 : ‖x‖ ^ 3 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have hne : ‖x ^ 4‖ ≠ ‖-(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0)‖ := by
      rw [norm_neg, norm_pow]; exact (hr.trans_lt h24).ne'
    rw [hφ, hψ, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_pow,
      max_eq_left (hr.trans h24.le), max_eq_left (hs.trans h34.le), max_eq_right hR1]

theorem max_norm_eq_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]),
    ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 →
      ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖
        ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 :=
  fun _ _ W h1 h2 h3 h4 h6 hΔ x => max_norm_eq W h1 h2 h3 h4 h6 hΔ x

end GlobalTheory.DupNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem eq_one_of_smul_haar_eq {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [LocallyCompactSpace H] (ν : Measure H) [ν.IsHaarMeasure] {c : NNReal} (h : c • ν = ν) :
    c = 1 := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have h1 : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (c : ENNReal) * ν K = 1 * ν K := by
    conv_rhs => rw [← h]
    rw [one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_left_inj h0 h1] at h2
  exact_mod_cast h2

theorem haar_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant := by
  intro p q T
  have h := blockOrd_finSumFinEquiv p q
  haveI := GlobalTheory.RealPar.SqInt.isHaarMeasure_map_covU h T
  set ε : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft
  set f := GlobalTheory.RealPar.SqInt.covU h T
  have hf : Measurable f := (GlobalTheory.RealPar.SqInt.continuous_covU h T).measurable
  obtain ⟨c, hc⟩ : ∃ c : NNReal, T.haar.map f = c • Formalism.REAL.muG ε :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hR : T.haar.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have hg := Measure.map_right_mul_eq_modularCharacterFun_smul T.haar g
    have h1 : (T.haar.map (· * g)).map f = T.haar.map f := by
      have h2 : (T.haar.map (· * g)).map f = (T.haar.map f).map (· * f g) := by
        rw [Measure.map_map hf (measurable_mul_const g), Measure.map_map (measurable_mul_const _) hf]
        congr 1
        ext x
        simp
      rw [h2, hc, Measure.map_smul, Formalism.REAL.indefinite_unitary_unimodular _ ε (f g)]
      exact (measurable_mul_const _).aemeasurable
    rw [hg, Measure.map_smul] at h1
    · rw [hg, eq_one_of_smul_haar_eq _ h1, one_smul]
    · exact hf.aemeasurable
  refine ⟨hR, ⟨?_⟩⟩
  haveI : T.haar.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨d, hd⟩ : ∃ d : NNReal, T.haar.inv = d • T.haar := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have h1 : T.haar.inv.map f = T.haar.map f := by
    have h2 : T.haar.inv.map f = (T.haar.map f).map (fun x => x⁻¹) := by
      rw [Measure.inv_def, Measure.map_map hf measurable_inv, Measure.map_map measurable_inv hf]
      congr 1
      ext x
      simp
    rw [h2, hc, Measure.map_smul, Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular _ ε]
    exact measurable_inv.aemeasurable
  rw [hd, Measure.map_smul] at h1
  · rw [hd, eq_one_of_smul_haar_eq _ h1, one_smul]
  · exact hf.aemeasurable

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicWeilRepresentationModelStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicWeilRepresentationModel : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  first | exact @GlobalTheory.FinWeil.Model.exists_isModel | exact GlobalTheory.FinWeil.Model.exists_isModel | (intros; apply GlobalTheory.FinWeil.Model.exists_isModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
section
noncomputable section
namespace GlobalTheory.CartanInt.UnitLog
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (a b : n) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single b (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ (EuclideanSpace.single b (1 : ℂ)))) a
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ (h2.trans h)
  simp

theorem exists_log {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n ℂ)
    (hu : u ∈ unitary (Matrix n n ℂ)) :
    ∃ H : Matrix n n ℂ, Hᴴ = H ∧ ‖H‖ ≤ Real.pi ∧ u = NormedSpace.exp (Complex.I • H) ∧
      ∀ J, Commute u J → Commute (star u) J → Commute H J := by
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  refine ⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp
  · refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
    simpa using Complex.abs_arg_le_pi z
  · rw [← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _),
      ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)]
    conv_lhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun z hz => ?_
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hsph z hz, mul_comm _ Complex.I] at this
    simpa using this.symm

theorem isKC_iff_commute {p q : ℕ} (X : Mat p q) : IsKC X ↔ Commute X (Formalism.UG.Jpq p q) := by
  constructor
  · intro h
    ext a b
    have h1 := h a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp_all [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · intro h a b hab
    have h1 := congrFun (congrFun h.eq a) b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢
    · linear_combination (-1 / 2 : ℂ) * h1
    · linear_combination (1 / 2 : ℂ) * h1

theorem exists_unitlog : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧
    (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  intro p q k hk
  have hu : (UpqT.mat k : Mat p q) ∈ unitary (Mat p q) :=
    Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hk)
  obtain ⟨H, h1, h2, h3, h4⟩ := exists_log _ hu
  refine ⟨H, h1, (isKC_iff_commute H).2 (h4 _ ((isKC_iff_commute _).1 hk) ?_),
    fun a b => (norm_entry_le H a b).trans h2, h3⟩
  rw [Matrix.star_eq_conjTranspose, ← mat_inv_of_mem_Kc hk]
  exact (isKC_iff_commute _).1 ((Ksg p q).inv_mem hk)

end GlobalTheory.CartanInt.UnitLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecompositionStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  first | exact @GlobalTheory.ThetaTranslDecomp.exists_decomp | exact GlobalTheory.ThetaTranslDecomp.exists_decomp | (intros; apply GlobalTheory.ThetaTranslDecomp.exists_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTotallyComplexExt
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open GlobalTheory.NormSum

namespace GlobalTheory.NormSum.Compare

theorem sqrt_le_rd (D : D7) : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem three_le (D : D7) : (3 : ℝ) ≤ D.host.q ∧ (3 : ℝ) ≤ D.host.d := by
  obtain ⟨hq, hd, -, hq2, hd2⟩ := D.host.hypOdd
  have := hq.two_le
  have := hd.two_le
  constructor
  · exact_mod_cast (show 3 ≤ D.host.q by omega)
  · exact_mod_cast (show 3 ≤ D.host.d by omega)

theorem log_d_le (D : D7) : Real.log D.host.d ≤ 2 * Real.log D.host.rdE := by
  obtain ⟨hq, hd⟩ := three_le D
  have h2 := sqrt_le_rd D
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity)
  have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have h5 : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by nlinarith
  have := Real.log_le_log (by linarith) h5
  rwa [Real.log_pow, Nat.cast_ofNat] at this

section Places

open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl)
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

end Places

end GlobalTheory.NormSum.Compare
end
end

