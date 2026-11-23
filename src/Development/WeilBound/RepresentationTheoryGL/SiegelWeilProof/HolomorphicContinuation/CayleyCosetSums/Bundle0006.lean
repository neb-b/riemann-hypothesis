module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0005
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Imports
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

private theorem exists_unitary_mul_blockTriangular_of_inFlagDomain (b : M2 n) (hb : InG b) : IsUnit (u1 b).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hr := congrArg (fun M => star x ⬝ᵥ (M *ᵥ x)) (v_rel b hb)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_sub,
    dotProduct_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_zero, zero_dotProduct,
    sub_zero, Matrix.zero_vecMul] at hr
  simp [Matrix.vecMul_smul] at hr
  have h2 : ∑ j, Complex.normSq (x j) = 0 := by
    have h3 := congrArg Complex.re hr
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.zero_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_apply]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _] at h2
  apply hx0
  funext j
  exact Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))

theorem factor (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det) :
    ∃ (R H0 : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ), IsUnit R.det ∧ H0.IsHermitian ∧ κ ≠ 0 ∧
      ∀ S, (u1 (y * nU S * b)).det = κ * (R * Rᴴ - Complex.I • (H0 + S)).det := by
  have hU := exists_unitary_mul_blockTriangular_of_inFlagDomain b hb
  have hH := hermit_cd y hy hc
  obtain ⟨U, hUdef⟩ : ∃ U, U = u1 b := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = v1 b := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = y.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = y.toBlocks₂₂ := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = V * U⁻¹ := ⟨_, rfl⟩
  have hrel : Uᴴ * V - Vᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hUdef, hVdef]
    exact v_rel b hb
  rw [← hUdef] at hU
  rw [← hCdef] at hc
  rw [← hCdef, ← hDdef] at hH
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hUU' : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hUU, Matrix.conjTranspose_one]
  have hP : P - Pᴴ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
    calc P - Pᴴ = ((U⁻¹)ᴴ * Uᴴ) * V * U⁻¹ - (U⁻¹)ᴴ * Vᴴ * (U * U⁻¹) := by
          rw [hUU', hUU, Matrix.one_mul, Matrix.mul_one, hPdef, Matrix.conjTranspose_mul]
      _ = (U⁻¹)ᴴ * (Uᴴ * V - Vᴴ * U) * U⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
          rw [hrel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hRR : (U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ = (U⁻¹)ᴴ * U⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose]
  have hI : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ) = (1 / 2 : ℂ) • (P - Pᴴ) := by
    rw [hRR, hP, smul_smul]
    congr 1
    ring
  refine ⟨(U⁻¹)ᴴ, (1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D, C.det * Complex.I ^ n * U.det, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr (Matrix.isUnit_nonsing_inv_det _ hU)
  · refine Matrix.IsHermitian.add ?_ hH
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · exact mul_ne_zero (mul_ne_zero hc.ne_zero (pow_ne_zero _ Complex.I_ne_zero)) hU.ne_zero
  · intro S
    have hin : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))
        = P + C⁻¹ * D + S := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, hI]
      module
    have e1 : C * P * U = C * V := by
      rw [hPdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    have e2 : C * (C⁻¹ * D) * U = D * U := by
      rw [← Matrix.mul_assoc C, Matrix.mul_nonsing_inv _ hc, Matrix.one_mul]
    have hmain : u1 (y * nU S * b) = C * (Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ
        - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))) * U := by
      rw [hin, second_coord_mul_inner, (nU_blocks y S).1, (nU_blocks y S).2, ← hCdef, ← hDdef, ← hUdef, ← hVdef]
      simp only [Matrix.mul_add, Matrix.add_mul]
      rw [e1, e2]
      abel
    rw [hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]
    ring

end PositivityTheory.Rg.Sw.HSt.L3
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockMulUnipotentDomain
section
noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem inverse_first_block_eq_cayley (x : M2 n) : ub1 x = (2 * Complex.I) • (Cmi n * x⁻¹).toBlocks₁₁ := by
  rw [toBlocks₁₁_mul', Cmi, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, ub1]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
  congr 1
  · rw [show (2 * Complex.I * (-Complex.I / 2)) = 1 by ring_nf; simp [Complex.I_sq]]; simp
  · congr 1; ring

theorem inverse_second_block_eq_cayley (x : M2 n) : ub2 x = (2 * Complex.I) • (Cmi n * x⁻¹).toBlocks₂₁ := by
  rw [toBlocks₂₁_mul, Cmi, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, ub2]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
  have h1 : (2 * Complex.I * (Complex.I / 2)) = -1 := by ring_nf; simp [Complex.I_sq]
  rw [h1]
  simp only [neg_smul, one_smul]
  congr 1
  congr 1; ring

theorem cmi_mul_cm : Cmi n * Cm n = 1 := by
  rw [← cm_inv]; exact Cinv_mul_Cm

theorem mX_mul_mX_neg (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    mX 1 Q R 1 * mX 1 (-Q) (-R) 1 = 1 := by
  rw [mX, mX, cm_inv, show Cm n * fromBlocks 1 Q R 1 * Cmi n * (Cm n * fromBlocks 1 (-Q) (-R) 1 * Cmi n) =
    Cm n * (fromBlocks 1 Q R 1 * (Cmi n * Cm n) * fromBlocks 1 (-Q) (-R) 1) * Cmi n by
      simp only [Matrix.mul_assoc]]
  rw [cmi_mul_cm, Matrix.mul_one, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, hQR, hRQ, neg_zero, add_zero, add_neg_cancel,
    neg_add_cancel, zero_add]
  rw [show fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = 1 from fromBlocks_one, Matrix.mul_one, cm_mul_cmi]

theorem mX_inv (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    (mX 1 Q R 1)⁻¹ = mX 1 (-Q) (-R) 1 := Matrix.inv_eq_right_inv (mX_mul_mX_neg Q R hQR hRQ)

theorem cmi_mX_neg (Q R : Matrix (Fin n) (Fin n) ℂ) :
    Cmi n * mX 1 (-Q) (-R) 1 = fromBlocks 1 (-Q) (-R) 1 * Cmi n := by
  rw [mX, cm_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, cmi_mul_cm, Matrix.one_mul]

theorem inverse_first_block_mul_unipotent (x : M2 n) (hx : IsUnit x.det) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    ub1 (x * mX 1 Q R 1) = ub1 x - Q * ub2 x := by
  have hM : IsUnit (mX 1 Q R 1).det := by
    have h := mX_mul_mX_neg Q R hQR hRQ
    exact Matrix.isUnit_det_of_right_inverse h
  rw [inverse_first_block_eq_cayley, inverse_first_block_eq_cayley, inverse_second_block_eq_cayley, Matrix.mul_inv_rev, mX_inv Q R hQR hRQ, ← Matrix.mul_assoc, cmi_mX_neg,
    Matrix.mul_assoc, toBlocks₁₁_mul', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.one_mul]
  rw [Matrix.mul_smul, smul_add, neg_mul, smul_neg, sub_eq_add_neg]

theorem u_ub_rel (x : M2 n) (hx : IsUnit x.det) : u1 x * ub1 x + u2 x * ub2 x = 0 := by
  rw [inverse_first_block_eq_cayley, inverse_second_block_eq_cayley, ← mul_cm₂₁, ← mul_cm₂₂, Matrix.mul_smul, Matrix.mul_smul, ← smul_add, ← toBlocks₂₁_mul,
    show x * Cm n * (Cmi n * x⁻¹) = x * (Cm n * Cmi n) * x⁻¹ by simp only [Matrix.mul_assoc], cm_mul_cmi,
    Matrix.mul_one, Matrix.mul_nonsing_inv _ hx]
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₁, smul_zero]

theorem inverse_first_block_mul_unipotent_domain (x : M2 n) (hx : x ∈ Dom n) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0)
    (hRQ : R * Q = 0) : ub1 (x * mX 1 Q R 1) = (1 + Q * wM x) * ub1 x := by
  rw [inverse_first_block_mul_unipotent x hx.1 Q R hQR hRQ]
  have h2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 hx.2.2.1
  have hrel := u_ub_rel x hx.1
  have e : ub2 x = -(wM x * ub1 x) := by
    have : u2 x * ub2 x = -(u1 x * ub1 x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hrel
    calc ub2 x = (u2 x)⁻¹ * (u2 x * ub2 x) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h2, Matrix.one_mul]
      _ = -(wM x * ub1 x) := by rw [this, Matrix.mul_neg, wM, Matrix.mul_assoc]
  rw [e, Matrix.mul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]

theorem det_mX_one (Q R : Matrix (Fin n) (Fin n) ℂ) (hRQ : R * Q = 0) : (mX 1 Q R 1).det = 1 := by
  rw [mX, det_mul, det_mul, det_fromBlocks_one₁₁, hRQ, sub_zero, det_one, mul_one, ← det_mul, Matrix.mul_nonsing_inv]
  · exact det_one
  · exact Matrix.isUnit_det_of_right_inverse cm_mul_cmi

theorem embOn_mul_embOn_compl (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    embOn (blkA j) T * embOn (blkB j) S = 0 ∧ embOn (blkB j) S * embOn (blkA j) T = 0 := by
  constructor <;> ext a b <;> simp only [Matrix.mul_apply, Matrix.zero_apply, embOn] <;>
    refine Finset.sum_eq_zero fun k _ => ?_ <;> by_cases hk : k ∈ blkA j <;> simp_all [blkB]

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KsTraceSingle
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem ks_inv_eq {U : Matrix (Fin n) (Fin n) ℂ} (h : U * Uᴴ = 1) : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h

theorem ks_trace_single (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : (X * Matrix.single a b 1).trace = X b a := by
  rw [Matrix.trace_mul_single]
  simp

theorem ks_rhoP {Kg : Type} [Group Kg] (ι : Kg →* M2 n) (m : ℕ) (k k1 : Kg) (hk : InK (ι k))
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : N ∈ unitaryGroup (Fin n) ℂ) (h1 : ι k1 = Proj.kM 1 N) :
    rhoP ι m 0 1 (k * k1) = fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
  obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) N (one_mem _) hN
  have hu1 : u1 (ι (k * k1)) = u1 (ι k) := by
    rw [map_mul, h1, ← hmk, first_block_mul_compact (ι k) hkk, hmk, Proj.first_unitary_block_of_pair, Matrix.mul_one]
  have hu2 : u2 (ι (k * k1)) = u2 (ι k) * N := by
    rw [map_mul, h1, ← hmk, second_block_mul_compact (ι k) hkk, hmk, Proj.second_unitary_block_of_pair]
  have U1 : u1 (ι k) * (u1 (ι k))ᴴ = 1 := first_cayley_block_unitary hk
  have U2 : u2 (ι k) * (u2 (ι k))ᴴ = 1 := second_cayley_block_unitary hk
  have UN : N * Nᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hN
    rwa [Matrix.star_eq_conjTranspose] at this
  have hfz : fz m 0 0 (ι (k * k1)) = (u1 (ι k)).det ^ (-(m : ℤ)) := by
    simp only [fz, zpow_zero, one_mul, neg_zero, Complex.cpow_zero, mul_one, hu1]
  have hne : (u1 (ι k)).det ≠ 0 := det_first_cayley_block_ne_zero hk.1
  have hd : star (u1 (ι k)).det = ((u1 (ι k)).det)⁻¹ := by
    have := congrArg Matrix.det U1
    rw [det_mul, det_one, det_conjTranspose] at this
    exact eq_inv_of_mul_eq_one_right this
  have hfV : fV (m : ℤ) 0 (ι k) = star ((u1 (ι k)).det ^ (-(m : ℤ))) := by
    have h := scalar_section_mul_conjugate_section hk (m : ℤ) 0
    have hf0 : f0 (m : ℤ) 0 (ι k) = (u1 (ι k)).det ^ (-(m : ℤ)) := by simp [f0]
    rw [hf0] at h
    rw [star_zpow₀, hd, eq_inv_of_mul_eq_one_right h]
    rw [_root_.zpow_neg, _root_.zpow_neg, _root_.inv_zpow, inv_inv]
  have htr : star ((u2 (ι (k * k1)))⁻¹ * 1 * u1 (ι (k * k1))).trace = ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
    rw [hu1, hu2, Matrix.mul_one, Matrix.mul_inv_rev, ← Matrix.trace_conjTranspose, ks_inv_eq UN, ks_inv_eq U2,
      ks_inv_eq U1]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold rhoP
  rw [star_mul', hfz, htr, hfV]

theorem ks_perm_unitary (a b : Fin n) : (Equiv.swap a b).permMatrix ℂ ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem ks_diag_unitary (b : Fin n) :
    Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1) ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = b <;> simp [h]

theorem ks_single_eq (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • (Equiv.swap a b).permMatrix ℂ +
      (1 / 2 : ℂ) • ((Equiv.swap a b).permMatrix ℂ * Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.single_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    smul_eq_mul]
  by_cases hj : j = b
  · subst hj
    by_cases hi : i = a
    · subst hi
      simp <;> norm_num
    · have : ¬ (Equiv.swap a j i = j) := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact hi
      simp [this, Ne.symm hi]
  · simp only [hj, if_false]
    by_cases h : Equiv.swap a b i = j
    · simp only [h, if_true]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring
    · simp only [h, if_false]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring

theorem kSplit : KSplit := by
  intro n m a0 b0 Kg _ ι hK
  classical
  set Pm : Matrix (Fin n) (Fin n) ℂ := (Equiv.swap a0 b0).permMatrix ℂ with hPmdef
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i = b0 then (1 : ℂ) else -1) with hDdef
  have hPm : Pm ∈ unitaryGroup (Fin n) ℂ := ks_perm_unitary a0 b0
  have hD : D ∈ unitaryGroup (Fin n) ℂ := ks_diag_unitary b0
  set Nl : Fin 2 → Matrix (Fin n) (Fin n) ℂ := ![Pm, Pm * D] with hNldef
  have hNl : ∀ l, Nl l ∈ unitaryGroup (Fin n) ℂ := by
    intro l
    fin_cases l
    · exact hPm
    · exact mul_mem hPm hD
  have hex : ∀ l, ∃ k1 : Kg, ι k1 = Proj.kM 1 (Nl l) := fun l => by
    obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) (Nl l) (one_mem _) (hNl l)
    have : InK (Proj.kM 1 (Nl l)) := by rw [← hmk]; exact hkk
    exact (hK _).1 this
  choose kl hkl using hex
  refine ⟨2, fun _ => 1 / 2, kl, fun k => ?_⟩
  have hk : InK (ι k) := (hK _).2 ⟨k, rfl⟩
  rw [Fin.sum_univ_two, ks_rhoP ι m k (kl 0) hk _ (hNl 0) (hkl 0), ks_rhoP ι m k (kl 1) hk _ (hNl 1) (hkl 1)]
  rw [← ks_trace_single ((u1 (ι k))⁻¹ * u2 (ι k)) a0 b0, ks_single_eq a0 b0]
  simp only [hNldef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LoweringDerivativeVacuum
section
noncomputable section

open Matrix Filter Topology Polynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem diffAt_of_cdo {f : M2 n → ℂ} {U : Set (M2 n)} (hf : ContDiffOn ℂ ∞ f U) (hU : IsOpen U) {x : M2 n}
    (hx : x ∈ U) : DifferentiableAt ℂ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

theorem D0_eq_numSeg_mul_add {x : M2 n} (hx : InG x) :
    (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
  rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def]
  exact Complex.mul_conj _

theorem normSq_det_first_block_pos {x : M2 n} (hx : InG x) : 0 < Complex.normSq (u1 x).det :=
  Complex.normSq_pos.mpr (det_first_block_ne_zero_group hx)

theorem det_product_mem_slitPlane {x : M2 n} (hx : InG x) : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
  rw [D0_eq_numSeg_mul_add hx]; exact Complex.ofReal_mem_slitPlane.mpr (normSq_det_first_block_pos hx)

theorem diff_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) : DifferentiableAt ℂ (fz m e z) x := by
  have hU : IsOpen {y : M2 n | det y ≠ 0} := isOpen_det_ne
  have hxU : x ∈ {y : M2 n | det y ≠ 0} := (isUnit_det_of_inG hx).ne_zero
  have hdet : DifferentiableAt ℂ (fun y : M2 n => det y) x :=
    diffAt_of_cdo (cdo_det (fun i j => (contDiff_apply_apply ℂ i j).contDiffOn)) hU hxU
  have hu1 : DifferentiableAt ℂ (fun y : M2 n => (u1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => LVs.contDiffOn_first_cayley_block_entries _ i j)) hU hxU
  have hub1 : DifferentiableAt ℂ (fun y : M2 n => (ub1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => PositivityTheory.Rg.Sw.HSt.LoweringDerivative.contDiffOn_inverse_first_block i j)) hU hxU
  unfold fz
  refine ((hdet.zpow (Or.inl hxU)).mul (hu1.zpow (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hu1.mul hub1).cpow (differentiableAt_const _) (det_product_mem_slitPlane hx)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_det_one_add_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • A).det) A.trace 0 := by
  have h : (fun s : ℂ => (1 + s • A).det) = fun s =>
      1 + A.trace * s + (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2 := by
    funext s
    exact Matrix.det_one_add_smul s A
  rw [h]
  have h1 : HasDerivAt (fun s : ℂ => 1 + A.trace * s) A.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul A.trace).const_add 1
  have h2 : HasDerivAt (fun s : ℂ =>
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2) 0 0 := by
    convert (Polynomial.hasDerivAt
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX (0 : ℂ)).fun_mul
      (hasDerivAt_pow 2 (0 : ℂ)) using 1
    all_goals first
      | rfl
      | simp
  convert h1.fun_add h2 using 1
  all_goals first
    | rfl
    | simp

set_option backward.isDefEq.respectTransparency false in
theorem lt1 : LoweringDerivativeVacuum := by
  intro n m e z Q x hx
  have hxu : IsUnit x := isUnit_of_inG hx
  have hD : (u1 x).det * (ub1 x).det ≠ 0 := Complex.slitPlane_ne_zero (det_product_mem_slitPlane hx)
  have hB : (ub1 x).det ≠ 0 := right_ne_zero_of_mul hD
  rw [rC_eq _ _ _ (diff_fz hx m e z), lowQ_eq]
  have hline : ∀ s : ℂ, x + s • (x * Nq Q) = x * (1 + s • Nq Q) := by
    intro s
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hsub : ∀ s : ℂ, ub1 x - s • (Q * ub2 x) = ub1 x * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))) := by
    intro s
    have hBu : IsUnit (ub1 x).det := isUnit_iff_ne_zero.2 hB
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul, smul_neg, sub_eq_add_neg]
  have hcomp : ∀ s : ℂ, fz m e z (x + s • (x * Nq Q)) = det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      ((u1 x).det * ((ub1 x).det * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))).det)) ^ (-z) := by
    intro s
    rw [hline s]
    unfold fz
    rw [det_lower, first_block_lowering_invariant, inverse_first_block_lowering hxu, hsub, Matrix.det_mul]
  have htr : (-((ub1 x)⁻¹ * (Q * ub2 x))).trace = -(Om x * Q).trace := by
    unfold Om
    rw [Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm Q]
  have hL : HasDerivAt (fun s : ℂ => x + s • (x * Nq Q)) (x * Nq Q) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const (x * Nq Q)).const_add x using 1
    all_goals first
      | rfl
      | simp
  have h1 : HasDerivAt (fun s : ℂ => fz m e z (x + s • (x * Nq Q)))
      (fderiv ℂ (fz m e z) x (x * Nq Q)) 0 :=
    (diff_fz hx m e z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_one_add_smul (-((ub1 x)⁻¹ * (Q * ub2 x)))
  have hg := (hdet.const_mul (ub1 x).det).const_mul (u1 x).det
  have hg0 : (u1 x).det * ((ub1 x).det * (1 + (0 : ℂ) • -((ub1 x)⁻¹ * (Q * ub2 x))).det)
      ∈ Complex.slitPlane := by
    simpa using det_product_mem_slitPlane hx
  have hp := (hg.cpow_const (c := -z) hg0).const_mul (det x ^ e * (u1 x).det ^ (-(m : ℤ)))
  have h2 := hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hcomp)
  rw [h1.unique h2, htr]
  simp only [zero_smul, add_zero, Matrix.det_one, mul_one]
  rw [Complex.cpow_sub _ _ hD, Complex.cpow_one]
  have hr : (u1 x).det * ((ub1 x).det * -(Om x * Q).trace) =
      -((u1 x).det * (ub1 x).det * (Om x * Q).trace) := by ring
  rw [hr]
  unfold eQ fz
  generalize (u1 x).det * (ub1 x).det = D at hD ⊢
  field_simp

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative

namespace PositivityTheory.Rg.Sw.HSt

theorem lt1 : LoweringDerivativeVacuum := LoweringDerivative.lt1

end PositivityTheory.Rg.Sw.HSt
end
end

