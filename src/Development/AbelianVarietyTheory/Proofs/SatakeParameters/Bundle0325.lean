module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulDetPowPolynomial
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

open Formalism.L2.KerInert.SharpPolyP

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def zA {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then (f τ).adjugate.transpose.submatrix id Fin.rev else f τ

def adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) : MvPolynomial (GL3Theta.FrV D n) ℂ :=
  MvPolynomial.aeval (fun k : GL3Theta.FrV D n => if IsOddPos (pos.symm k.1).2 then
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (k.1, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate (Fin.rev k.2.2) k.2.1
    else MvPolynomial.X k) Q

theorem eval_adj {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (i j : Fin n) :
    MvPolynomial.eval (pt x) ((Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate i j)
      = (x τ).adjugate i j := by
  have h := congrArg (fun M => M i j) (RingHom.map_adjugate (MvPolynomial.eval (pt x))
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)))
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [h]
  congr 1
  ext a b
  simp

theorem eval_adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (pt x) (adjPol X D pos Q) = MvPolynomial.eval (pt (zA X D pos x)) Q := by
  unfold adjPol
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X q k hq =>
    rw [map_mul, map_mul, hq, map_mul]
    congr 1
    rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
    show _ = zA X D pos x k.1 k.2.1 k.2.2
    unfold zA
    split_ifs with h
    · rw [eval_adj]; rfl
    · rw [MvPolynomial.eval_X]

def dg {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun _ => if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1

theorem zT_eq_mul {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos x = fun τ => zA X D pos x τ * dg X D pos x τ := by
  funext τ
  unfold zT zA dg
  split_ifs with h
  · ext i j
    simp [Matrix.mul_diagonal, Matrix.inv_def, Ring.inverse_eq_inv', mul_comm]
  · simp

theorem dg_bor {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    IsBor (dg X D pos x) := by
  intro τ
  refine ⟨fun r s hsr => ?_, fun r => ?_⟩
  · unfold dg
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hsr)
  · unfold dg
    rw [Matrix.diagonal_apply_eq]
    split_ifs
    · exact inv_ne_zero (hx τ)
    · exact one_ne_zero

theorem eval_zT {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (hQ : Q ∈ WtPol ℂ ν)
    (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    MvPolynomial.eval (pt (zT X D pos x)) Q =
      (∏ τ, ∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        MvPolynomial.eval (pt x) (adjPol X D pos Q) := by
  rw [eval_adjPol, zT_eq_mul, ← sp_eval_colSub (dg X D pos x) (zA X D pos x) Q, hQ _ (dg_bor X D pos x hx),
    MvPolynomial.smul_eval]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun r _ => ?_
  unfold dg
  rw [Matrix.diagonal_apply_eq]

theorem twF_mul_det_poly : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}, 0 < n → ∀ (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ (K : D.what₂.Tau → ℕ) (P : MvPolynomial (GL3Theta.FrV D n) ℂ), ∀ x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (x τ).det ≠ 0) → MvPolynomial.eval (fun k : GL3Theta.FrV D n => x k.1 k.2.1 k.2.2) P = twF X D pos c Q x * ∏ τ, (x τ).det ^ K τ := by
  intro p _ X D pos n hn ν c hc Q hQ
  have hc0 : ∀ τ, 0 ≤ c τ := fun τ => le_trans (Int.natCast_nonneg _) (hc τ ⟨0, hn⟩)
  refine ⟨fun τ => if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0,
    (∏ τ, if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) * adjPol X D pos Q, ?_⟩
  intro x hx
  change MvPolynomial.eval (pt x) _ = _
  have key : ∀ τ, MvPolynomial.eval (pt x) (if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) =
      (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) *
        (∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        (x τ).det ^ (if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0) := by
    intro τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, c τ = m := ⟨(c τ).toNat, (Int.toNat_of_nonneg (hc0 τ)).symm⟩
    have hd := hx τ
    rw [det_zT]
    split_ifs with h
    · rw [map_mul, map_pow, MvPolynomial.eval_C, sp_eval_frDet, hm, Int.toNat_natCast, zpow_neg, zpow_natCast,
        Finset.prod_pow_eq_pow_sum, mul_assoc, ← mul_pow, inv_mul_cancel₀ hd, one_pow, mul_one, mul_pow, mul_inv,
        inv_pow, inv_inv]
    · simp
  unfold twF
  rw [map_mul, map_prod, Finset.prod_congr rfl (fun τ _ => key τ), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  change _ = _ * MvPolynomial.eval (pt (zT X D pos x)) Q * _
  rw [eval_zT X D pos ν Q hQ x hx]
  ring

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulUpperTriangular
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem upper_inv_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hU : ∀ r s, s < r → M r s = 0) (hd : ∀ r, M r r ≠ 0) :
    (∀ r s, s < r → M⁻¹ r s = 0) ∧ ∀ r, M⁻¹ r r = (M r r)⁻¹ := by
  classical
  have hB : Matrix.BlockTriangular M id := fun i j h => hU i j h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hB]
    exact Finset.prod_ne_zero_iff.2 fun r _ => hd r
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  letI := M.invertibleOfIsUnitDet hunit
  have hBi : Matrix.BlockTriangular M⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun r s h => hBi h, fun i => ?_⟩
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_right h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hU i k hk, zero_mul]
    · rw [hBi hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem zT_mul {n : ℕ} (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ *
      (if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ) := by
  funext τ
  unfold zT
  split_ifs with h
  · rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact (Equiv.sum_comp Fin.revPerm (fun k => ((x τ)⁻¹).transpose i k * ((β τ)⁻¹).transpose k (Fin.rev j))).symm
  · rfl

theorem prod_inv_rev_zpow_mul_prod_pow_eq_odd_position {n : ℕ} (b : Fin n → ℂ) (hb : ∀ r, b r ≠ 0) (c : ℤ) (ν : Fin n → ℕ) (h : ∀ r, (ν r : ℤ) ≤ c) :
    (∏ r, (b (Fin.rev r))⁻¹) ^ (-c) * ∏ r, (b (Fin.rev r))⁻¹ ^ ν r = ∏ r, b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat := by
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp Fin.revPerm (fun r => b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat)]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have e : b (Fin.rev r) ^ (c - (ν r : ℤ)).toNat = b (Fin.rev r) ^ (c - (ν r : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by linarith [h r])]
  rw [e, inv_zpow', neg_neg, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hb _)]
  congr 1

theorem twF_mul_bor : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∀ (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (x τ).det ≠ 0) → IsBor β → twF X D pos c Q (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) * twF X D pos c Q x := by
  intro p _ X D pos n ν c hνc Q hQ x β _hx hβ
  classical
  have hbd : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
  have hinv : ∀ τ, (∀ r s, s < r → ((β τ)⁻¹) r s = 0) ∧ ∀ r, ((β τ)⁻¹) r r = (β τ r r)⁻¹ :=
    fun τ => upper_inv_diag (β τ) (hβ τ).1 (hbd τ)
  let β' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ
  have hd' : ∀ τ r, β' τ r r = if IsOddPos (pos.symm τ).2 then (β τ (Fin.rev r) (Fin.rev r))⁻¹ else β τ r r := by
    intro τ r
    simp only [β']
    split_ifs
    · simp [(hinv τ).2]
    · rfl
  have hB' : IsBor β' := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [β']
      split_ifs
      · simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
        exact (hinv τ).1 _ _ (Fin.rev_lt_rev.2 hsr)
      · exact (hβ τ).1 r s hsr
    · rw [hd']
      split_ifs
      · exact inv_ne_zero (hbd τ _)
      · exact hbd τ r
  have hz : zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ * β' τ := zT_mul X D pos x β
  have hev : GL3Theta.evFr D Q (fun τ => zT X D pos x τ * β' τ) =
      (∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x) := by
    have h1 := Formalism.L2.KerInert.SharpPolyP.sp_eval_colSub β' (zT X D pos x) Q
    rw [hQ β' hB', MvPolynomial.smul_eval] at h1
    exact h1.symm
  have key : ∀ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r
      = (∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) *
        (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) := by
    intro τ
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [Matrix.det_mul, Formalism.L2.KerInert.SharpPolyP.sp_det_bor hB', mul_zpow]
      simp only [hd', if_pos ho]
      rw [← prod_inv_rev_zpow_mul_prod_pow_eq_odd_position (fun r => β τ r r) (hbd τ) (c τ) (ν τ) (hνc τ)]
      ring
    · simp only [if_neg ho, one_mul, mul_one, hd']
  unfold twF
  rw [hz, hev]
  calc (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) *
        ((∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x))
      = (∏ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r) *
          GL3Theta.evFr D Q (zT X D pos x) := by rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp_rw [key]; rw [Finset.prod_mul_distrib]; ring

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLattices
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FrameLat

theorem colSpan_mul' (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M g : Matrix (Fin k) (Fin k) K) :
    Formalism.MainNotions.G.colSpan R (M * g) = (Formalism.MainNotions.G.colSpan R g).map ((M.mulVecLin).restrictScalars R) := by
  unfold Formalism.MainNotions.G.colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem latMap_pair' (D : D7) {p : ℕ} (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K)
    (hu : ∀ s : ℕ, Nat.Coprime s p → IsUnit (s : R)) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin N') (Fin N') K)
    (hG : Formalism.MainNotions.G.colSpan R G = locSp R ρ L) (hG' : Formalism.MainNotions.G.colSpan R G' = locSp R ρ L')
    (B : Matrix (Fin N') (Fin N) D.host.E) (hB : ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L')
    (hL : Formalism.BasicNotions.IsSDLat D.host.E N L) (hL' : Formalism.BasicNotions.IsSDLat D.host.E N' L') :
    (∀ c, (B.map ρ) *ᵥ (fun x => G x c) ∈ Formalism.MainNotions.G.colSpan R G') ∧
    (∀ c, (B.map (fun y => ρ (D.host.conj y)))ᵀ *ᵥ (fun x => G' x c) ∈ Formalism.MainNotions.G.colSpan R G) := by
  obtain ⟨s, hs, hB'⟩ := hB
  constructor
  · intro c
    rw [hG']
    refine locSp_maps_of_unit_smul R K ρ L L' B s (hu s hs) hB' _ ?_
    rw [← hG]
    exact Submodule.subset_span ⟨c, rfl⟩
  · intro c
    have e : (B.map (fun y => ρ (D.host.conj y)))ᵀ = ((B.map D.host.conj)ᵀ).map ρ := by
      ext a b
      rfl
    rw [e, hG]
    refine locSp_maps_of_unit_smul R K ρ L' L _ s (hu s hs) (adj_maps_sd D L L' B s hL hL' hB') _ ?_
    rw [← hG']
    exact Submodule.subset_span ⟨c, rfl⟩

end GlobalTheory.TwV.FrameLat


open GlobalTheory.TwV.FrameLat in
theorem GlobalTheory.TwV.frameLatMapLt_of_ties : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧ ∀ v, locSp (X.G.P.W v) (ρ v) (fd.kerN j La) = (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧ locSp (X.G.P.W v) (ρ v) (fd.kerN (j + 1) La') = (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))) → Lt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ := by
  intro p _ X _ hfin D fd ρ hA hT
  intro j hj L0 hL0 La' hLa' φ r b hb _ i v
  have hL0' : (X.Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat X.Lv hfin j L0 hL0
  obtain ⟨hAd, hK⟩ := hT j hj L0 La' hL0' hLa'
  obtain ⟨hK1, hK2⟩ := hK v
  refine latMap_pair' D (X.G.P.W v) (ρ v) (natCast_isUnit_localRing X v) (Formalism.L2.KerInert.RepFrame.Gm X fd.frM φ v)
    (Formalism.L2.KerInert.RepFrame.Gp X fd.frM φ v) ?_ ?_ (b i)
    (GlobalTheory.TwV.YYMaps.locBasis_maps D p hA _ _ b hb i) hAd.2.2.1 hAd.2.2.2
  · rw [hK1]
    unfold Formalism.L2.KerInert.RepFrame.Gm
    rw [colSpan_mul', ← φ.hg v]
  · rw [hK2]
    unfold Formalism.L2.KerInert.RepFrame.Gp
    rw [colSpan_mul', ← φ.hg' v]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PolarizedSat

theorem hasSat_conjPlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  intro hF E _ _ _ a π χ hpol
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (compNorm E χ).UnrAt w :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) B :=
    (conjSrc_injective _).tendsto_cofinite.eventually (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π)
  filter_upwards [hu, hs] with w hw hB'e B hB
  obtain ⟨B', hB'⟩ := hB'e
  have e := UpperTheory.V.Br.satOfPol E a π _ hpol.dual w hw B B' hB hB'
  have e2 : B' = B.map fun α => α⁻¹ * (compNorm E χ).val w := by
    have e3 := congrArg (Multiset.map fun z : ℂˣ => z⁻¹) e
    rw [Multiset.map_map, Multiset.map_map] at e3
    simp only [Function.comp_def, inv_inv, Multiset.map_id'] at e3
    rw [e3]
    exact Multiset.map_congr rfl fun α _ => by rw [mul_inv_rev, inv_inv, mul_comm]
  rw [← e2]
  exact hB'

end GlobalTheory.PolarizedSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.QuadCharUnr

theorem quadChar_unrAt_of_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hw : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))
    · exact GlobalTheory.LFun.isUnram_of_isSplit h2 hs
    · refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
      obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl
      haveI := u.isPrime
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw
  intro x hx
  have hn := GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (localIdele _ _ x)) = 1
  rw [GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]

end GlobalTheory.QuadCharUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScalInvFrame
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA

theorem scal_inv_frame : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → Formalism.L2.G.Pend.cA X Kc j (BOf fd j La) = ι (∏ τ, embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j τ))) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j La n h M hU hF
  have hMu : IsUnit (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det M).isUnit
  have hdet : ∀ v, (fd.frM j La v).det = ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    intro v
    rw [hF v, Matrix.det_submatrix_equiv_self, RingHom.map_det]
    rfl
  have hu : ∀ v, IsUnit (fd.frM j La v).det := fun v => by rw [hdet v]; exact hMu.map (ρ v)
  have hfr : ∀ v, ((frGL fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) = fd.frM j La v := by
    intro v; unfold frGL; rw [dite_eq_left (hu v)]; rfl
  have hB : ∀ v s, tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det =
      (tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det))⁻¹ := by
    intro v s
    have h1 : ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det * (fd.frM j La v).det = 1 := by
      rw [← hfr v, ← Matrix.det_mul]
      unfold BOf
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 := congrArg (tw X Kc v s) h1
    rw [map_mul, map_one, hdet v] at h2
    exact eq_inv_of_mul_eq_one_left h2
  unfold Formalism.L2.G.Pend.cA
  have hterm : ∀ v s, (tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^
      ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s) =
      ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos ⟨v, s⟩)))) := by
    intro v s
    rw [hB v s, (GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU v s).2, map_zpow₀]
    simp only [wT]
    rw [Equiv.symm_apply_apply]
    split_ifs <;> simp [zpow_neg, inv_inv]
  simp_rw [hterm]
  rw [map_prod]
  exact (Fintype.prod_sigma (fun x => ι (embT D (pos x) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos x)))))).symm.trans
    (Fintype.prod_equiv pos _ _ (fun _ => rfl))

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem sNum_lev_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ _
  exact Formalism.L2.Ker.level_structure_counting D L hT Gi Gl Kc Dx cX ex t u μ

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem pos_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  exact GlobalTheory.TwU.lamPos_of_posEmb (sysS H X std) S.E.toCEmb D _ S.lam _ (ex.cmp.embW u w hg) S.hK (J.Gd.cmp.tie u w hg).pos_emb

end GlobalTheory.TwV
end
end

