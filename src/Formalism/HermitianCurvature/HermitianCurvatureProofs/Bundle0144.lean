module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearFormRadicalRankOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0141

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlkUUMapMuPRn
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section alg

variable {k r : ℕ}

theorem eI_eB' (a : Fin r) : eI k r a = eB k r 0 (Sum.inl (Sum.inl a)) := by
  ext; rw [Ux3.block_index_first_val]; rfl

theorem blkU_uMap (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    blkU (C2.uMap k r z g) = Matrix.of fun a b => g (eI k r a) (eI k r b) := by
  ext a b
  simp only [blkU, Matrix.submatrix_apply, C2.uMap, Matrix.of_apply]
  rw [dite_eq_left (by simp), fvec_low z b.castSucc (by simp), herm_bvec_esI', mulVec_bvec_apply]
  rfl

theorem muP_Rn_blk (W : Matrix (Fin r) (Fin r) ℂ) (y : U.RC k r 0) (a b : Fin r) :
    (U.muP k r 0 W * U.Rn k r 0 y) (eI k r a) (eI k r b) = W a b := by
  rw [eI_eB', eI_eB', U.muP, Ux3.rn_eq, Ux3.block3_mul, Ux3.block3_apply]
  simp

theorem blkU_uMap_muP_Rn (z : Fin (2 * r + k + 1) → ℂ) (W : Matrix (Fin r) (Fin r) ℂ) (y : U.RC k r 0) :
    blkU (C2.uMap k r z (U.muP k r 0 W * U.Rn k r 0 y)) = W := by
  rw [blkU_uMap]; ext a b; exact muP_Rn_blk W y a b

theorem xiTau_one {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau S (1, 1) p = psi k r S.z cStd (Matrix.of p.1.2) * star (psi k r S.z' cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau psi B.lam
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul]
  push_cast; ring

theorem leviElement_superdiagonal_entry (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (W : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    (if h : a.val + 1 < r then (U.muP k r 0 W) (eI k r a) (eI k r ⟨a.val + 1, h⟩)
      else (U.muP k r 0 W *ᵥ z) (eI k r a)) = (if h : a.val + 1 < r then W a ⟨a.val + 1, h⟩ else 0) := by
  split_ifs with h
  · rw [eI_eB', eI_eB', U.muP, Ux3.block3_apply]; simp
  · rw [eI_eB', mulVec_eB, U.muP]
    simp only [Ux3.block3_apply]
    simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromRows_apply_inl, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hz _ (Or.inl (by rw [Ux3.block_index_first_val]; exact c.isLt)), mul_zero]

theorem psi_muP (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) (W : Matrix (Fin r) (Fin r) ℂ) :
    psi k r z c (U.muP k r 0 W) = C2.psiC c (C2.simpleUp W) := by
  have hell : ell k r z (U.muP k r 0 W) = C2.simpleUp W := by
    unfold ell C2.simpleUp
    exact Finset.sum_congr rfl fun a _ => leviElement_superdiagonal_entry z hz W a
  unfold psi C2.psiC
  rw [hell]

theorem simpleUp_mul {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) (hB : B ∈ C2.UTset m) :
    C2.simpleUp (A * B) = C2.simpleUp A + C2.simpleUp B := by
  unfold C2.simpleUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · set b : Fin m := ⟨a.val + 1, h⟩
    have hab : a ≠ b := by intro e; have := congrArg Fin.val e; simp [b] at this
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
    · rw [hA.2 a, hB.2 b, one_mul, mul_one, add_comm]
    · intro c ⟨hca, hcb⟩
      by_cases hc : c < a
      · rw [hA.1 a c hc, zero_mul]
      · have hc' : b < c := by
          have h1 : a < c := lt_of_le_of_ne (not_lt.1 hc) (Ne.symm hca)
          rw [Fin.lt_def] at h1 ⊢
          have : c.val ≠ a.val + 1 := fun e => hcb (Fin.ext e)
          simp [b]; omega
        rw [hB.1 c b hc', mul_zero]
  · simp

theorem gaXi_zero (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0) :
    U.gaXi k 0 σ d ξ (fun a => a.elim0) γ =
      (U.Rn k r 0 ξ.1.1)⁻¹ * U.mMap k r 0 (U.headH σ d ξ.2.2.1 ξ.2.2.2) γ * U.Rn k r 0 ξ.1.2 := by
  unfold U.gaXi U.ZjH
  rw [Dx2.SL.zj_zero]
  rfl

theorem psiStar_zero (σ : Equiv.Perm (Fin r)) (z z' : Fin (2 * (r + 0 + 0) + k + 1) → ℂ) (ξ : U.Xi k r 0 0 σ) :
    U.psiStar k 0 σ z z' ξ = psi k r z cStd (U.Rn k r 0 ξ.1.1) * star (psi k r z' cStd (U.Rn k r 0 ξ.1.2)) *
      G.psi U.betaU (U.subS (U.wP σ * U.lowW σ ξ.2.2.1 * (U.wP σ)⁻¹) + U.supS (G.upper ξ.2.2.2)) := by
  unfold U.psiStar U.psiH
  simp only [Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero, add_zero]
  rfl

theorem gv_unit {ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ B.GV k ρ) : IsUnit y.det := by
  have := B2x5.normSq_det_GV hy
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, Complex.normSq_zero] at this; exact zero_ne_one this

theorem sgs_formula (z0 z0' : Fin (2 * 0 + k + 1) → ℂ) (h h' : Mt k r)
    (hh : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0)) (hh' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0'))
    (V V' : G.UT r → ℂ) (y y' : U.RC k r 0) (Z : Matrix (Fin r) (Fin r) ℂ) (γ0 : B.Mat k 0) :
    B.sgs ((h, psiR k r (y, V)), (h', psiR k r (y', V'))) (U.mMap k r 0 Z γ0) =
      (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h))⁻¹ y))⁻¹ *
        U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) *
        U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h'))⁻¹ y') := by
  set y1 := midB r 0 (Matrix.of h) with hy1def
  set y1' := midB r 0 (Matrix.of h') with hy1def'
  have hy1 : y1 ∈ UWset k 0 z0 := uw_mid r 0 z0 _ hh
  have hy1' : y1' ∈ UWset k 0 z0' := uw_mid r 0 z0' _ hh'
  have hH : (Matrix.of h : B.Mat k (r + 0)) = U.embG k r 0 y1 := by
    rw [← Dx2.Tower.lev_eq_embG, uw_block r 0 z0 _ hh]
  have hH' : (Matrix.of h' : B.Mat k (r + 0)) = U.embG k r 0 y1' := by
    rw [← Dx2.Tower.lev_eq_embG, uw_block r 0 z0' _ hh']
  have u1 := gv_unit hy1.1
  have uE : IsUnit (U.embG k r 0 y1).det := by
    rw [← Dx2.Tower.lev_eq_embG]; exact gv_unit (Dx2.Tower.lev_GV r 0 y1 hy1.1)
  have uE' : IsUnit (U.embG k r 0 y1').det := by
    rw [← Dx2.Tower.lev_eq_embG]; exact gv_unit (Dx2.Tower.lev_GV r 0 y1' hy1'.1)
  have uV : IsUnit (G.upper V).det := Dx2.SL.isUnit_up V
  have uRn : IsUnit (U.Rn k r 0 y).det := by
    refine Matrix.isUnit_det_of_right_inverse (B := U.Rn k r 0 (-y)) ?_
    exact PBM.rn_mul_neg y

  have hM1 : (U.muP k r 0 (G.upper V))⁻¹ * U.mMap k r 0 Z γ0 * U.muP k r 0 (G.upper V') =
      U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') γ0 := by
    rw [leviElement_inv _ uV, BigCellDiagonalMap.leviElement_mul_mMap _ _ _ ((G.upper V).isUnit_nonsing_inv_det uV), Ux4.mMap_mul_muP,
      Matrix.conjTranspose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_conjTranspose]; exact uV.star)]
  unfold B.sgs
  simp only [psiR, Matrix.of.apply_symm_apply]
  rw [hH, hH']
  set E := U.embG k r 0 y1
  set E' := U.embG k r 0 y1'
  have e1 : (U.Rn k r 0 (rnAct y1⁻¹ y))⁻¹ = E⁻¹ * (U.Rn k r 0 y)⁻¹ * E := by
    rw [← embG_conj_Rn y1 hy1.1 y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ uE,
      Matrix.mul_assoc]
  have e2 : U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') (y1⁻¹ * γ0 * y1') =
      E⁻¹ * U.mMap k r 0 ((G.upper V)ᴴ * Z * G.upper V') γ0 * E' := (embG_conj_mMap y1 y1' u1 _ γ0).symm
  have e3 : U.Rn k r 0 (rnAct y1'⁻¹ y') = E'⁻¹ * U.Rn k r 0 y' * E' := (embG_conj_Rn y1' hy1'.1 y').symm
  rw [e1, e2, e3, ← hM1, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ uE, Matrix.mul_nonsing_inv_cancel_left _ _ uE']

theorem conjS_UT {w0 : Equiv.Perm (Fin r)} {d0 : Fin r → ℂ} (hd0 : ∀ a, d0 a ≠ 0) (x0 : C2.Lstidx w0 → ℂ) :
    (C2.monoP w0 d0)⁻¹ * StabilizerDisintegration.lowS w0 x0 * C2.monoP w0 d0 ∈ C2.UTset r :=
  (Dx2.Rad.low_mem w0 d0 hd0 x0).2

theorem orbit_split {w0 : Equiv.Perm (Fin r)} {d0 : Fin r → ℂ} (hd0 : ∀ a, d0 a ≠ 0) (x0 : C2.Lstidx w0 → ℂ)
    (y2 : C2.LPidx w0 → ℂ) (V' : G.UT r → ℂ) :
    (G.upper (StabilizerDisintegration.UC.fSp w0 (x0, y2)))ᴴ * C2.monoP w0 d0 * G.upper V' =
      StabilizerDisintegration.lowP w0 y2 * C2.monoP w0 d0 *
        G.upper (StabilizerDisintegration.utc ((C2.monoP w0 d0)⁻¹ * StabilizerDisintegration.lowS w0 x0 * C2.monoP w0 d0 * G.upper V')) := by
  have hP := Formalism.FourierDecayAlt.P.C2x2.isUnit_det_monomialMatrix w0 d0 hd0
  rw [StabilizerDisintegration.UC.upper_fSp, StabilizerDisintegration.UC.upper_utc (Formalism.FourierDecayAlt.P.C2x2.ut_mul (conjS_UT hd0 x0) (StabilizerDisintegration.UC.upper_mem V')),
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem mMap_mul_mMap {ρ : ℕ} (Z Y : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det) (hY : IsUnit Y.det)
    (γ : B.Mat k ρ) (hγ : IsUnit γ.det) :
    U.mMap k r ρ Zᴴ γ⁻¹ * U.mMap k r ρ Y γ = U.muP k r ρ (Z⁻¹ * Y) := by
  have hZH : IsUnit Zᴴ.det := by rw [Matrix.det_conjTranspose]; exact hZ.star
  have hYH : IsUnit Yᴴ.det := by rw [Matrix.det_conjTranspose]; exact hY.star
  unfold U.mMap U.muP
  rw [Ux3.block3_mul]
  congr 1
  · simp only [Matrix.mul_zero, zero_add, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (G.wMat r), Ux3.wMat_mul_self, Matrix.one_mul]
  all_goals try simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  · exact Matrix.nonsing_inv_mul _ hγ
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hZH]
    simp only [Matrix.mul_assoc]

theorem conj_muP (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det) (γ0 : B.Mat k 0) (hγ0 : IsUnit γ0.det)
    (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : IsUnit Q.det) :
    (U.mMap k r 0 Z γ0)⁻¹ * U.muP k r 0 Q * U.mMap k r 0 Z γ0 = U.muP k r 0 (Z⁻¹ * (Qᴴ)⁻¹ * Z) := by
  have hQH : IsUnit (Qᴴ)⁻¹.det := by
    rw [Matrix.det_nonsing_inv, Matrix.det_conjTranspose]; exact (hQ.star).ringInverse
  rw [mMap_inv Z γ0 hZ hγ0, Matrix.mul_assoc, BigCellDiagonalMap.leviElement_mul_mMap _ _ _ hQ,
    mMap_mul_mMap Z _ hZ (by rw [Matrix.det_mul]; exact hQH.mul hZ) γ0 hγ0, Matrix.mul_assoc]

theorem relevance_U {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det)
    (γ0 : B.Mat k 0) (hγ0 : IsUnit γ0.det) (hrel : C6.IsRelevant S (U.mMap k r 0 Z γ0))
    (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q ∈ C2.UTset r) (hQ' : Z⁻¹ * (Qᴴ)⁻¹ * Z ∈ C2.UTset r) :
    C2.psiC cStd (C2.simpleUp Q) = C2.psiC cStd (C2.simpleUp (Z⁻¹ * (Qᴴ)⁻¹ * Z)) := by
  have uQ : IsUnit Q.det := by rw [StabilizerDisintegration.UC.det_UT hQ]; exact isUnit_one
  have hN : ∀ A : Matrix (Fin r) (Fin r) ℂ, A ∈ C2.UTset r → U.muP k r 0 A ∈ Formalism.QuantumDeterminants.Nset k (r + 0) :=
    fun A hA => BigCellDiagonalMap.leviElement_nset A ⟨fun i j hij => hA.1 i j hij, hA.2⟩
  have hρ : U.muP k r 0 Q ∈ C6.Rset (U.mMap k r 0 Z γ0) := by
    refine ⟨hN Q hQ, ?_⟩
    rw [conj_muP Z hZ γ0 hγ0 Q uQ]; exact hN _ hQ'
  have h := hrel.2 _ hρ
  rw [conj_muP Z hZ γ0 hγ0 Q uQ, psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem] at h
  exact h

end alg

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

theorem liftVec_eB (u : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    liftVec k p ρ u (U.eB k p ρ x) = Sum.elim (Sum.elim (fun _ => 0) u) (fun _ => 0) x := by
  rcases x with (a | b) | c
  · have ha := a.isLt
    simp only [liftVec, Sum.elim_inl]
    rw [dite_eq_right]
    simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
    omega
  · have hb := b.isLt
    simp only [liftVec, Sum.elim_inl, Sum.elim_inr]
    rw [dite_eq_left]
    · congr 1
      ext
      simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
      omega
    · simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
      omega
  · have hc := c.isLt
    simp only [liftVec, Sum.elim_inr]
    rw [dite_eq_right]
    simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]
    omega

theorem inWb_liftVec {z : Fin (2 * ρ + k + 1) → ℂ} (hz : inWb k ρ z) : inWb k (p + ρ) (liftVec k p ρ z) := by
  intro i hi
  simp only [liftVec]
  split_ifs with h
  · exact hz _ (by show i.val - p < ρ ∨ ρ + k < i.val - p; omega)
  · rfl

theorem eI_X (a : Fin p) : eI k (p + ρ) (Fin.castAdd ρ a) = U.eB k p ρ (Sum.inl (Sum.inl a)) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

theorem eI_V (a : Fin ρ) : eI k (p + ρ) (Fin.natAdd p a) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ a))) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

theorem eI_V' (a : ℕ) (ha : a < ρ) (h : p + a < p + ρ) :
    eI k (p + ρ) ⟨p + a, h⟩ = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨a, ha⟩))) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

theorem eI_X' (a : ℕ) (ha : a < p) (h : a < p + ρ) :
    eI k (p + ρ) ⟨a, h⟩ = U.eB k p ρ (Sum.inl (Sum.inl ⟨a, ha⟩)) := by
  ext
  simp only [U.eB, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, eI]

private theorem embG_eB_inl_inl_apply_eq_ite (y : B.Mat k ρ) (a : Fin p) (x : U.Ix k p ρ) :
    U.embG k p ρ y (U.eB k p ρ (Sum.inl (Sum.inl a))) (U.eB k p ρ x) = if x = Sum.inl (Sum.inl a) then 1 else 0 := by
  rcases x with (a' | b') | c' <;> simp [U.embG, Ux6.block3_apply, Matrix.one_apply] <;> (try split_ifs) <;> simp_all

private theorem embG_mulVec_liftVec_eB_apply (y : B.Mat k ρ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    (U.embG k p ρ y *ᵥ liftVec k p ρ z) (U.eB k p ρ x) =
      Sum.elim (Sum.elim (fun _ => 0) (y *ᵥ z)) (fun _ => 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (U.eB k p ρ)]
  simp only [U.embG, Ux6.block3_apply, liftVec_eB]
  rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem ell_embG (z : Fin (2 * ρ + k + 1) → ℂ) (y : B.Mat k ρ) :
    ell k (p + ρ) (liftVec k p ρ z) (U.embG k p ρ y) = ell k ρ z y := by
  simp only [Formalism.QuantumDeterminants.ell]
  rw [Fin.sum_univ_add, Finset.sum_eq_zero, zero_add]
  · apply Finset.sum_congr rfl
    intro b _
    have hb := b.isLt
    have hV : eI k (p + ρ) (Fin.natAdd p b) = U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ b))) := eI_V b
    by_cases h : b.val + 1 < ρ
    · have h' : (Fin.natAdd p b).val + 1 < p + ρ := by simp; omega
      have hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩))) := eI_V' (b.val + 1) h (by simp; omega)
      rw [dite_eq_left h', dite_eq_left h, hV, hV']
      simp [U.embG, Ux6.block3_apply]
    · have h' : ¬ (Fin.natAdd p b).val + 1 < p + ρ := by simp; omega
      rw [dite_eq_right h', dite_eq_right h, hV, embG_mulVec_liftVec_eB_apply]
      rfl
  · intro a _
    have ha := a.isLt
    rw [eI_X a]
    split_ifs with h
    · obtain ⟨x, hx⟩ := (U.eB k p ρ).surjective (eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h⟩)
      rw [← hx, embG_eB_inl_inl_apply_eq_ite, if_neg]
      rintro rfl
      have := congrArg Fin.val hx
      simp [U.eB, eI] at this
    · rw [embG_mulVec_liftVec_eB_apply]
      rfl

private theorem muP_mulVec_liftVec_eB_apply (q : Matrix (Fin p) (Fin p) ℂ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.Ix k p ρ) :
    (U.muP k p ρ q *ᵥ liftVec k p ρ z) (U.eB k p ρ x) = Sum.elim (Sum.elim (fun _ => 0) z) (fun _ => 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (U.eB k p ρ)]
  simp only [U.muP, Ux6.block3_apply, liftVec_eB]
  rcases x with (a | b) | c <;> simp [Fintype.sum_sum_type, Matrix.one_apply]

theorem ell_muP (z : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (q : Matrix (Fin p) (Fin p) ℂ) :
    ell k (p + ρ) (liftVec k p ρ z) (U.muP k p ρ q) = U.supS q := by
  simp only [Formalism.QuantumDeterminants.ell, U.supS]
  rw [Fin.sum_univ_add]
  refine (congrArg₂ HAdd.hAdd ?_ (Finset.sum_eq_zero fun b _ => ?_)).trans (add_zero _)
  · apply Finset.sum_congr rfl
    intro a _
    have ha := a.isLt
    rw [eI_X a]
    by_cases h : a.val + 1 < p
    · have h' : (Fin.castAdd ρ a).val + 1 < p + ρ := by simp; omega
      have hX' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inl ⟨a.val + 1, h⟩)) := eI_X' (a.val + 1) h h'
      rw [dite_eq_left h', dite_eq_left h, hX']
      simp [U.muP, Ux6.block3_apply]
    · rw [dite_eq_right h]
      split_ifs with h'
      · have hρ : 0 < ρ := by simp at h'; omega
        have hV' : eI k (p + ρ) ⟨(Fin.castAdd ρ a).val + 1, h'⟩ =
            U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨0, hρ⟩))) := by
          ext
          simp [U.eB, eI] <;> omega
        rw [hV']
        simp [U.muP, Ux6.block3_apply]
      · rw [muP_mulVec_liftVec_eB_apply]
        rfl
  · have hb := b.isLt
    rw [eI_V b]
    split_ifs with h'
    · have h : b.val + 1 < ρ := by simp at h'; omega
      have hV' : eI k (p + ρ) ⟨(Fin.natAdd p b).val + 1, h'⟩ =
          U.eB k p ρ (Sum.inl (Sum.inr (eI k ρ ⟨b.val + 1, h⟩))) := eI_V' (b.val + 1) h (by simp; omega)
      have hne : eI k ρ b ≠ eI k ρ ⟨b.val + 1, h⟩ := by
        intro e
        have := congrArg Fin.val e
        simp [eI] at this
      rw [hV']
      simp [U.muP, Ux6.block3_apply, Matrix.one_apply, hne]
    · rw [muP_mulVec_liftVec_eB_apply]
      exact hz _ (Or.inl (by simp [eI]))

theorem psi_of_ell {r r' : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r)
    (g' : B.Mat k r') (h : ell k r z g = ell k r' z' g') : psi k r z cStd g = psi k r' z' cStd g' := by
  simp only [Formalism.QuantumDeterminants.psi, h]

theorem psi_measure_preserving : PsiMuP := by
  intro k p ρ z' u hz
  simp only [Formalism.QuantumDeterminants.psi, G.psi, U.betaU, ell_muP z' hz]
  show (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [neg_mul, Complex.ofReal_neg]
  ring

theorem upper_isUpUni (u : G.UT p → ℂ) : Formalism.DoubleCosetMeasures.IsUpUni (G.upper u) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
    simp [G.upper, G.strictUpper, Matrix.one_apply, h1, h2]
  · simp [G.upper, G.strictUpper]

theorem rn_nset (x : U.RC k p ρ) : U.Rn k p ρ x ∈ QuantumDeterminants.Nset k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨x, rfl⟩)

theorem psi_right_equivariant : PsiRight := by
  intro k p ρ z' ν' u x hz hν
  have hz0 := inWb_liftVec (p := p) hz
  have hcl := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)
  have h1 := embG_nset (p := p) hν
  have h2 := Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset (k := k) (ρ := ρ) _ (upper_isUpUni u)
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ (hcl.mul_mem _ h1 _ h2) (rn_nset x),
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset _ hz0 _ h1 h2, psi_of_ell _ z' _ ν' (ell_embG z' ν')]

theorem corner_block_action_invariant (y : B.Mat k ρ) (x : U.RC k p ρ) (v : Fin (2 * ρ + k + 1) → ℂ) (hy : yᴴ * Hpk k ρ * y = Hpk k ρ)
    (hv : y *ᵥ v = v) :
    (-(G.wMat p * (Matrix.of (rcAct y x).1)ᴴ * Hpk k ρ)) *ᵥ v = (-(G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ)) *ᵥ v := by
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have hv' : yᴴ *ᵥ (Hpk k ρ *ᵥ v) = Hpk k ρ *ᵥ v := by
    calc yᴴ *ᵥ (Hpk k ρ *ᵥ v) = yᴴ *ᵥ (Hpk k ρ *ᵥ (y *ᵥ v)) := by rw [hv]
      _ = (yᴴ * Hpk k ρ * y) *ᵥ v := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Hpk k ρ *ᵥ v := by rw [hy]
  have h2 : (G.wMat p * (Matrix.of x.1)ᴴ * yᴴ * Hpk k ρ) *ᵥ v = (G.wMat p * (Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ v := by
    simp only [← Matrix.mulVec_mulVec, hv']
  rw [h1, Matrix.conjTranspose_mul, Matrix.neg_mulVec, Matrix.neg_mulVec, ← Matrix.mul_assoc, h2]

theorem psi_right_action_comm : PsiRnAct := by
  intro k p ρ z' h' x hz hh
  have hz0 := inWb_liftVec (p := p) hz
  apply psi_of_ell
  rw [Ux3.rn_eq, Ux3.rn_eq, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0, Formalism.FourierDecayAlt.P.PBH.ell_uni _ hz0]
  by_cases hp : 0 < p
  · rw [dite_eq_left hp, dite_eq_left hp]
    by_cases hρ : 0 < ρ
    · rw [dite_eq_left hρ, dite_eq_left hρ]
      have e := congrFun (corner_block_action_invariant h' x (bvec (eI k ρ ⟨0, hρ⟩)) hh.1 (hh.2.1 ⟨0, hρ⟩).1) ⟨p - 1, by omega⟩
      have e2 : ∀ M : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ,
          M ⟨p - 1, by omega⟩ ⟨0, by omega⟩ = (M *ᵥ bvec (eI k ρ ⟨0, hρ⟩)) ⟨p - 1, by omega⟩ := by
        intro M; simp only [bvec, Matrix.mulVec_single_one]; rfl
      exact (e2 _).trans (e.trans (e2 _).symm)
    · rw [dite_eq_right hρ, dite_eq_right hρ]
      have hlow : U.lowV k p ρ (liftVec k p ρ z') = z' := by
        funext q; simp only [U.lowV, liftVec]; rw [dite_eq_left (by omega)]; congr 1; ext; simp
      rw [hlow]
      exact congrFun (corner_block_action_invariant h' x z' hh.1 hh.2.2) _
  · rw [dite_eq_right hp, dite_eq_right hp]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRWirt
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rot_alg (ζ D1 DI : ℂ) : -(ζ.im : ℂ) * D1 + (ζ.re : ℂ) * DI =
    Complex.I * (ζ * ((1 / 2 : ℂ) * (D1 + -Complex.I * DI)) - star ζ * ((1 / 2 : ℂ) * (D1 + Complex.I * DI))) := by
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hs : star ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hz +
    ((Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hs + ((ζ.re : ℂ) * DI - (ζ.im : ℂ) * D1) * Complex.I_sq

theorem rotation_wirtinger_holds : GTRRWirt := by
  intro r u x hu
  have h1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I))
      (Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I) * (1 * Complex.I)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp
  have h2 : HasDerivAt (fun φ : ℝ => x.2 * Complex.exp ((φ : ℂ) * Complex.I)) (x.2 * Complex.I) 0 := by
    have h3 := h1.const_mul x.2
    simpa using h3
  have hγ : HasDerivAt (fun φ : ℝ => ((x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E r))
      ((0 : Fin r → ℂ), x.2 * Complex.I) 0 := by
    first
    | exact (hasDerivAt_const (0 : ℝ) x.1).prodMk h2
    | exact (hasDerivAt_const (0 : ℝ) x.1).prod h2
  have hx : x = ((x.1, x.2 * Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I)) : MA.E r) := by simp
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hx
  have hdir1 : MA.dirE (M.vz (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vz]
  have hdir2 : MA.dirE (M.vzb (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vzb]
  have hw1 : MA.wirt M.vz u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      -Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir1]
    simp [M.vz]
  have hw2 : MA.wirt M.vzb u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir2]
    simp [M.vzb]
  have key : Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x) =
      fderiv ℝ u x ((0 : Fin r → ℂ), x.2 * Complex.I) := by
    rw [hw1, hw2, ← rot_alg]
    have hv : ((0 : Fin r → ℂ), x.2 * Complex.I) = x.2.re • ((0 : Fin r → ℂ), Complex.I) +
        (-x.2.im) • ((0 : Fin r → ℂ), (1 : ℂ)) := by
      refine Prod.ext (by simp) ?_
      simp only [Prod.smul_snd, Prod.snd_add, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp
    rw [hv, map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [key]
  exact hc

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

