module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMoment
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0045

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin

theorem hermitian_pair_one_coordinates (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] =
      G 0 0 + G 0 1 * b + (starRingEnd ℂ) a * G 1 0 + (starRingEnd ℂ) a * G 1 1 * b := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem gram_identity (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) (a₀ a₁ : ℂ) :
    (herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 =
      G.det.re * ‖a₁ - a₀‖ ^ 2 := by
  have h10 : G 1 0 = (starRingEnd ℂ) (G 0 1) := (hG.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 1 1)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Matrix.det_fin_two,
    hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, h10]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, h00, h11]
  ring

theorem hermitian_pair_one_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have hne : (![1, a] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 0
  have h := hG.dotProduct_mulVec_pos hne
  exact (Complex.lt_def.mp h).1

theorem det_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.lt_def.mp hG.det_pos).1

theorem logSin_eq_log_add_xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) (hG : G.PosDef) (hne : a₀ ≠ a₁) :
    logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  have hA := hermitian_pair_one_re_pos G hG a₀
  have hB := hermitian_pair_one_re_pos G hG a₁
  have hD := det_re_pos G hG
  have hn : 0 < ‖a₁ - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hid := gram_identity G hG.1 a₀ a₁
  unfold logSin xiPot
  set A := (herm2 G ![1, a₀] ![1, a₀]).re
  set B := (herm2 G ![1, a₁] ![1, a₁]).re
  set C := ‖herm2 G ![1, a₀] ![1, a₁]‖
  set D := G.det.re
  set n := ‖a₁ - a₀‖
  have harg : 1 - C ^ 2 / (A * B) = D * n ^ 2 / (A * B) := by
    rw [← hid]
    field_simp
  rw [harg, Real.log_div (by positivity) (by positivity), Real.log_mul hD.ne' (by positivity),
    Real.log_mul hA.ne' hB.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalized
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

theorem densW (d k i : ℕ) (hi : i < k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z =
      (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 0 *
          f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 1 *
          f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then (0 : ℝ) else 1) * α (Fin.tail (Fin.tail z)))
    (p₀ p₁ : ℂ) :
    maDens φ (Fin.cons p₀ (Fin.cons p₁ y)) = (2 / Real.pi) ^ (d + 2) * (wS p₀ * wS p₁ *
      (L (rename some (aeval ![lin3 (nS p₀), lin3 (nS p₁)]
        (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) *
          X none ^ (d + 2 - 2 * k))).re) := by
  set uu : Fin (d + 2) → Fin 2 → ℝ := fun r => if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0
  set vv : Fin (d + 2) → ℝ := fun r => if (r : ℕ) < 2 * k then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons p₀ (Fin.cons p₁ y))) = fun r =>
      blk ((uu r 0 : ℂ) * -(wS p₀ : ℂ)) (blk ((uu r 1 : ℂ) * -(wS p₁ : ℂ))
        ((∑ j, ((uu r 0 * nS p₀ j + uu r 1 * nS p₁ j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H)) := by
    funext r
    have e : φ r = fun z : Fin (d + 2) → ℂ => uu r 0 * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        uu r 1 * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + vv r * α (Fin.tail (Fin.tail z)) :=
      funext (hφ r)
    rw [e, _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square d f α y p₀ p₁ _ _ _ _ (uu r 0) (uu r 1) (vv r) (hfc _) (hfc _) hα (hfh _) (hfh _), ← hH]
    congr 3
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two d T H L hL uu vv (nS p₀) (nS p₁) (-(wS p₀ : ℂ)) (-(wS p₁ : ℂ))
  rw [_root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd.evalW_pderiv_prod_rows_word d k i hi hkd (nS p₀) (nS p₁)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  rw [show (((d + 2).factorial : ℕ) : ℂ) = (((d + 2).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, neg_mul_neg, ← Complex.ofReal_mul, Complex.re_ofReal_mul] at hre
  rw [mul_right_comm, hre]
  ring

theorem densY (d k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z = (if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0) * f z +
        (if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1) * α (Fin.tail z))
    (a : ℂ) :
    maDens φ (Fin.cons a y) = (2 / Real.pi) ^ (d + 1) * (-(wS a) * (2 * (k : ℝ) - 1) *
      (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re) := by
  set cc : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0
  set vv : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons a y)) = fun r =>
      blk ((cc r : ℂ) * -(wS a : ℂ))
        ((∑ j, ((cc r * nS a j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H) := by
    funext r
    have e : φ r = fun z : Fin (d + 1) → ℂ => cc r * f z + vv r * α (Fin.tail z) := funext (hφ r)
    rw [e, _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre d f α y a _ _ (cc r) (vv r) (hfc _) hα (hfh _), ← hH]
    congr 2
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one d T H L hL cc vv (nS a) (-(wS a : ℂ))
  rw [_root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW d k hk hkd (nS a)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  have hR : (-(wS a : ℂ) * L (C (2 * (k : ℝ) - 1) * rename some (lin3 (nS a) ^ (2 * k - 2)) *
      X none ^ (d + 2 - 2 * k))).re = -(wS a) * (2 * (k : ℝ) - 1) *
        (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re := by
    rw [mul_assoc (C _), C_mul', map_smul, Complex.real_smul, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  rw [show (((d + 1).factorial : ℕ) : ℂ) = (((d + 1).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, hR] at hre
  rw [mul_right_comm, hre]
  ring

theorem fibre_integral_normal : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  intro h d k hk hkd G α y hPD hG2 hα hG1 hGd
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition d G y hPD hG2 hG1 hGd
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional d T (hessC α y)
  set f : (Fin (d + 1) → ℂ) → ℝ := fun z => xiPot (G (Fin.tail z)) (z 0) with hf
  have hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y) := fun a => (hT a).1
  have hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j) := by
    intro a
    rw [(hT a).2]
    ext p q
    refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
    · simp [blk, wS]
    · simp [blk]
    · simp [blk]
    · simp [blk, nS, Matrix.sum_apply]
  let ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ L ∘ₗ
    (LinearMap.mulRight ℝ (X none ^ (d + 2 - 2 * k) : MvPolynomial (Option (Fin 3)) ℝ)) ∘ₗ
      (rename some : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ).toLinearMap
  have hℓ : ∀ p, (L (rename some p * X none ^ (d + 2 - 2 * k))).re = ℓ p := fun p => rfl
  have hword : ∀ i ∈ Finset.range k, (∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) =
      (2 / Real.pi) ^ (d + 2) * (Real.pi ^ 2 * ℓ (diagWordMomentPoly k i)) := by
    intro i hi
    have hik := Finset.mem_range.1 hi
    have hpt : ∀ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 / Real.pi) ^ (d + 2) * (logSin 1 p.1 p.2 * (wS p.1 * wS p.2 *
          ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)]
            (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))))) := by
      intro p
      rw [densW d k i hik hkd T _ L hL f α y hfc hα hfh rfl _ ?_ p.1 p.2, hG1, hℓ]
      · ring
      · intro r z
        have hcoef : ∀ c : Fin 2, (if (r : ℕ) = 0 then (![1, -1] : Fin 2 → ℝ) c else if (r : ℕ) = 1 then (![0, 1] : Fin 2 → ℝ) c else if (r : ℕ) < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) = DiagonalFibreFubini.wordCoef i r c := by
          intro c
          simp only [DiagonalFibreFubini.wordCoef]
          split_ifs <;> rfl
        by_cases hr : (r : ℕ) < 2 * k
        · simp only [hr, if_true, hcoef, hf, Fin.tail, Fin.cons_zero, Fin.cons_succ]
          simp
        · simp [hr]
    simp_rw [hpt]
    rw [integral_const_mul, _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment, DiagonalFibreFubini.linProd_word k i hik]
    rfl
  have hY : ∀ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) =
      (2 / Real.pi) ^ (d + 1) * (-(2 * (k : ℝ) - 1)) * (wS a * ℓ (lin3 (nS a) ^ (2 * k - 2))) := by
    intro a
    rw [densY d k hk hkd T _ L hL f α y hfc hα hfh rfl _ ?_ a, hℓ]
    · ring
    · intro r z
      by_cases hr : (r : ℕ) < 2 * k - 1
      · simp [hr, hf]
      · simp [hr]
  have hfib : fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.1 k (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h2
  have hpush : pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.2.2.1 k hk (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl hword, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum,
    DiagFibreMoment.sum_diagWordMomentPoly, hfib]
  simp_rw [hY]
  rw [integral_const_mul, _root_.GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one]
  have hp : (-(2 * (k : ℝ) - 1)) * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ (2 * k - 2))) =
      -ℓ ((∑ i, X i ^ 2) ^ (k - 1)) := by
    rw [← map_neg, ← hpush, pushMomentPoly, map_smul, smul_eq_mul]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [C_mul', map_smul, smul_eq_mul]
  calc _ = (2 / Real.pi) ^ (d + 1) * (2 / Real.pi) * Real.pi ^ 2 * (-kappa k * ℓ ((∑ i, X i ^ 2) ^ (k - 1))) := by
        rw [pow_succ]; ring
    _ = 2 * kappa k * ((2 / Real.pi) ^ (d + 1) * (Real.pi * (-ℓ ((∑ i, X i ^ 2) ^ (k - 1))))) := by
        field_simp
    _ = _ := by
        rw [← hp]; ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem mul_elem_apply (A : Matrix (Fin N) (Fin N) ℂ) (ca cb r s : Fin N) (t : ℂ) :
    (A * (1 + Matrix.single cb ca t)) r s = A r s + if s = ca then A r cb * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply]
  by_cases h : s = ca
  · subst h
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h, Ne.symm h]

theorem elem_mul_elem {ca cb : Fin N} (hne : ca ≠ cb) (t u : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca u) =
      1 + Matrix.single cb ca (t + u) := by
  ext r s
  rw [mul_elem_apply]
  by_cases h : s = ca
  · subst h
    by_cases hr : cb = r
    · subst hr
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne]
      try ring
    · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne, hr, Ne.symm hr]
  · simp [Matrix.add_apply, Matrix.single_apply, h, Ne.symm h]

theorem mul_elem_cancel {ca cb : Fin N} (hne : ca ≠ cb) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    A * (1 + Matrix.single cb ca t) * (1 + Matrix.single cb ca (-t)) = A := by
  rw [Matrix.mul_assoc, elem_mul_elem hne, add_neg_cancel, Matrix.single_zero, add_zero, Matrix.mul_one]

theorem isBlockDiag_elem {ca cb : Fin N} (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem isLowerUni_mul_elem {ca cb : Fin N} (hlt : ca < cb) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsLowerUni A)
    (t : ℂ) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [mul_elem_apply, hA.1]
    split_ifs with h
    · subst h
      rw [hA.2 r cb hlt, zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hA.2 r s hrs]
    split_ifs with h
    · subst h
      rw [hA.2 r cb (hrs.trans hlt), zero_mul, add_zero]
    · rw [add_zero]

theorem isBlockDiag_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lc τ ca cb c τ') := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  unfold FC.Lc
  rw [dif_neg (fun h => hrs h.1.2), if_neg hne]

theorem isLowerUni_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsLowerUni (FC.Lc τ ca cb c τ') := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_irrefl _ h.1.1), if_pos rfl]
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_asymm hrs h.1.1), if_neg hrs.ne]

theorem Lc_apply_idx (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (q : FC.CIdx Ψ N j τ ca cb) :
    FC.Lc τ ca cb c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q := by
  unfold FC.Lc
  rw [dif_pos (⟨q.1.2, q.2⟩ : _ ∧ _)]

theorem Lc_self_apply (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (c : FC.CIdx Ψ N j τ ca cb → ℂ) :
    FC.Lc τ ca cb c τ cb ca = 0 := by
  unfold FC.Lc
  rw [dif_neg (fun h => h.2 rfl), if_neg (Ne.symm hne)]

theorem Lc_of_entries (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (L : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) (h0 : L τ cb ca = 0) :
    FC.Lc τ ca cb (fun q : FC.CIdx Ψ N j τ ca cb => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) = L := by
  funext τ'
  ext r s
  unfold FC.Lc
  split_ifs with h hrs
  · rfl
  · subst hrs
    exact ((hL τ').2.1 r).symm
  · by_cases e : (τ', r, s) = (τ, cb, ca)
    · obtain ⟨rfl, rfl, rfl⟩ : τ' = τ ∧ r = cb ∧ s = ca := by simpa using e
      exact h0.symm
    · have hn : ¬ (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) := fun h' => h ⟨h', e⟩
      by_cases hsr : s < r
      · exact ((hL τ').1 r s fun hb => hn ⟨hsr, hb⟩).symm
      · exact ((hL τ').2.2 r s (lt_of_le_of_ne (not_lt.1 hsr) hrs)).symm

theorem Lc_analytic (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ := by
  unfold FC.Lc
  by_cases h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca)
  · simp only [dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : FC.CIdx Ψ N j τ ca cb => ℂ)
      ⟨⟨(τ', r, s), h.1⟩, h.2⟩).analyticOnNhd _
  · simp only [dif_neg h]
    exact analyticOnNhd_const

theorem exists_Lca (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L := by
  have hne : ca ≠ cb := hlt.ne
  let a : ℂ := L τ cb ca
  let L' : Ψ → Matrix (Fin N) (Fin N) ℂ := Function.update L τ (L τ * (1 + Matrix.single cb ca (-a)))
  have hτ : L' τ = L τ * (1 + Matrix.single cb ca (-a)) := Function.update_self _ _ _
  have hL' : ∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [hτ]
      exact ⟨(hL _).1.mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (hL _).2 _⟩
    · have : L' τ' = L τ' := Function.update_of_ne e _ _
      rw [this]
      exact hL τ'
  have h0 : L' τ cb ca = 0 := by
    rw [hτ, mul_elem_apply, if_pos rfl, (hL τ).2.1 cb, one_mul]
    exact add_neg_cancel _
  refine ⟨fun q => L' q.1.1.1 q.1.1.2.1 q.1.1.2.2, a, ?_⟩
  have hback : L τ * (1 + Matrix.single cb ca (-a)) * (1 + Matrix.single cb ca a) = L τ := by
    have := mul_elem_cancel hne (L τ) (-a)
    rwa [neg_neg] at this
  unfold FC.Lca
  rw [Lc_of_entries τ hne L' hL' h0, hτ, hback]
  funext τ'
  by_cases e : τ' = τ
  · subst e
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne e]
    exact Function.update_of_ne e _ _

theorem Lca_prop (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ') := by
  unfold FC.Lca
  by_cases e : τ' = τ
  · subst e
    rw [Function.update_self]
    exact ⟨(isBlockDiag_Lc _ _ _ _ _).mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (isLowerUni_Lc _ _ _ _ _) _⟩
  · rw [Function.update_of_ne e]
    exact ⟨isBlockDiag_Lc _ _ _ _ _, isLowerUni_Lc _ _ _ _ _⟩

theorem Lca_injective (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ)
    (h : FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a') : c = c' ∧ a = a' := by
  have hne : ca ≠ cb := hlt.ne
  have hτ : FC.Lc τ ca cb c τ * (1 + Matrix.single cb ca a) = FC.Lc τ ca cb c' τ * (1 + Matrix.single cb ca a') := by
    have := congrFun h τ
    unfold FC.Lca at this
    rwa [Function.update_self, Function.update_self] at this
  have entry : ∀ (d : FC.CIdx Ψ N j τ ca cb → ℂ) (t : ℂ),
      (FC.Lc τ ca cb d τ * (1 + Matrix.single cb ca t)) cb ca = t := fun d t => by
    rw [mul_elem_apply, if_pos rfl, Lc_self_apply τ hne, (isLowerUni_Lc τ ca cb d τ).1 cb, zero_add, one_mul]
  have ha : a = a' := by
    rw [← entry c a, hτ, entry]
  subst ha
  have hc : FC.Lc τ ca cb c = FC.Lc τ ca cb c' := by
    funext τ'
    by_cases e : τ' = τ
    · subst e
      rw [← mul_elem_cancel hne (FC.Lc τ' ca cb c τ') a, hτ, mul_elem_cancel hne]
    · have := congrFun h τ'
      unfold FC.Lca at this
      rwa [Function.update_of_ne e, Function.update_of_ne e] at this
  refine ⟨funext fun q => ?_, rfl⟩
  rw [← Lc_apply_idx τ ca cb c q, hc, Lc_apply_idx]

theorem lc_main : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  intro Ψ _ _ N j τ ca cb hlt hs
  refine ⟨fun c τ' => ⟨isBlockDiag_Lc τ ca cb c τ', ?_⟩, fun τ' r s => Lc_analytic τ ca cb τ' r s,
    fun L hL => exists_Lca τ hlt hs L hL, fun c a τ' => Lca_prop τ hlt hs c a τ',
    fun c c' a a' h => Lca_injective τ hlt c c' a a' h⟩
  rw [(isLowerUni_Lc τ ca cb c τ').det]
  exact one_ne_zero

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_ne_zero_iff_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b z z' p h
  obtain ⟨c, hc, rfl⟩ := h
  unfold FC.plk
  cases hb : M.blk p with
  | none => simp
  | some k =>
    simp only [Option.elim, mul_left_comm _ (c k), ← Finset.mul_sum, ne_eq, mul_eq_zero, hc k, false_or]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

