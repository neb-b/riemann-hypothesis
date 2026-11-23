module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0020

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
section
noncomputable section

open scoped Matrix ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayIn : AwayIn := by
  intro D n V θ l s τ ε fr hθ hs hfr hl Ψ hΨ
  refine ⟨fun x x' hx hf => AwayPf.dep θ V l s τ hΨ x x' hx hf, fun f hf => ?_⟩
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, hp, rfl⟩ := hφ
    exact AwayPf.gen_sch θ V l s τ fr hfr.1 hs hl p hp g hg f hf
  | zero =>
    have : tens θ τ fr f (0 : Mx D V.rank n → ℂ) = 0 := by
      funext x
      simp [tens]
    rw [this]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens θ τ fr f (a + b) = tens θ τ fr f a + tens θ τ fr f b := by
      funext x
      simp only [tens, Pi.add_apply, mul_add]
    rw [this]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens θ τ fr f (c • a) = c • tens θ τ fr f a := by
      funext x
      simp only [tens, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ c ha

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockLowerRightMulBlockMatrix
section
noncomputable section

open Matrix GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob.Gen2H

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem submatrix_fromBlocks_levi (P Q S T : Matrix (Fin n) (Fin n) R) :
    (blk4 P Q S T).submatrix finSumFinEquiv finSumFinEquiv = fromBlocks P Q S T := by
  unfold blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem block_lower_right_mul_block_matrix (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (P Q S T : Matrix (Fin n) (Fin n) R) :
    blkDm (M * blk4 P Q S T) =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ * Q +
        (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ * T := by
  unfold blkDm
  rw [← Matrix.submatrix_mul_equiv M (blk4 P Q S T) finSumFinEquiv finSumFinEquiv finSumFinEquiv, submatrix_fromBlocks_levi]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]

theorem block_matrix_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv (fromBlocks a b c d) (fromBlocks a' b' c' d') finSumFinEquiv.symm finSumFinEquiv.symm
    finSumFinEquiv.symm, Matrix.fromBlocks_multiply]

theorem vecMul_mix (C D : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)) (u : Fin n → R) (j : Fin n) :
    vecMul u (C * eI I + D * (1 - eI I)) j = if j ∈ I then vecMul u C j else vecMul u D j := by
  classical
  have h2 : (1 : Matrix (Fin n) (Fin n) R) - eI I = diagonal (fun i => if i ∈ I then (0 : R) else 1) := by
    rw [eI, ← diagonal_one, diagonal_sub]
    congr 1; funext i; split_ifs <;> simp
  rw [h2, eI, vecMul_add, Pi.add_apply, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_diagonal, vecMul_diagonal]
  split_ifs <;> simp

end Ring

section Field

variable {k : Type} [Field k] {n : ℕ}

theorem cT_fromBlocks (σ : k →+* k) (A B C D : Matrix (Fin n) (Fin n) k) :
    Formalism.UG.cT σ (fromBlocks A B C D) =
      fromBlocks (Formalism.UG.cT σ A) (Formalism.UG.cT σ C) (Formalism.UG.cT σ B) (Formalism.UG.cT σ D) := by
  simp [Formalism.UG.cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cT_submatrix (σ : k →+* k) (M : Matrix (Fin (n + n)) (Fin (n + n)) k) :
    (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv =
      Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) := by
  ext i j
  rfl

theorem lower_rel (σ : k →+* k) (g : GL (Fin (n + n)) k) (hg : g ∈ Formalism.UG.UJ σ (J2 k n)) :
    let Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv
    Gs.toBlocks₂₁ * Formalism.UG.cT σ Gs.toBlocks₂₂ = Gs.toBlocks₂₂ * Formalism.UG.cT σ Gs.toBlocks₂₁ := by
  intro Gs
  have h0 : Formalism.UG.cT σ (g : Matrix (Fin (n + n)) (Fin (n + n)) k) * J2 k n * (g : Matrix (Fin (n + n)) (Fin (n + n)) k) =
      J2 k n := hg
  set J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k := fromBlocks 0 1 (-1) 0 with hJ'
  have hJs : (J2 k n).submatrix finSumFinEquiv finSumFinEquiv = J' := by rw [J2, submatrix_fromBlocks_levi]
  have h1 : Formalism.UG.cT σ Gs * J' * Gs = J' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h0
    rw [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _,
      cT_submatrix, hJs] at this
    exact this
  have hJJ : J' * J' = -1 := by
    rw [hJ', Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  have h2 : (-J' * Formalism.UG.cT σ Gs * J') * Gs = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT σ Gs), h1, Matrix.neg_mul, hJJ, neg_neg]
  have h3 : Gs * (-J' * Formalism.UG.cT σ Gs * J') = 1 := mul_eq_one_comm.mp h2
  have h4 : Gs * J' * Formalism.UG.cT σ Gs = J' := by
    calc Gs * J' * Formalism.UG.cT σ Gs = Gs * J' * Formalism.UG.cT σ Gs * (J' * J') * (-1) := by rw [hJJ]; noncomm_ring
      _ = (Gs * (-J' * Formalism.UG.cT σ Gs * J')) * J' := by noncomm_ring
      _ = J' := by rw [h3, Matrix.one_mul]
  have h5 := congrArg Matrix.toBlocks₂₂ h4
  conv_lhs at h5 => rw [← Matrix.fromBlocks_toBlocks Gs, cT_fromBlocks, hJ']
  rw [hJ', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.toBlocks_fromBlocks₂₂] at h5
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h5
  rw [neg_add_eq_zero] at h5
  exact h5.symm

theorem lower_inj (g : GL (Fin (n + n)) k) (u : Fin n → k)
    (hC : u ᵥ* ((g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (hD : u ᵥ* ((g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 0) :
    u = 0 := by
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  let w : Fin n ⊕ Fin n → k := Sum.elim 0 u
  have hw : w ᵥ* Gs = 0 := by
    funext x
    rcases x with i | i
    · have := congrFun hC i
      simpa [w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using this
    · have := congrFun hD i
      simpa [w, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂] using this
  have hdet : Gs.det ≠ 0 := by
    rw [hGs, Matrix.det_submatrix_equiv_self]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hw0 : w = 0 := by
    by_contra hne
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨w, hne, hw⟩)
  funext j
  have := congrFun hw0 (Sum.inr j)
  simpa [w] using this

theorem conj_vecMul (σ : k →+* k) (u' : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) (i : Fin n) :
    σ ((u' ᵥ* Y) i) = (Formalism.UG.cT σ Y *ᵥ (fun l => σ (u' l))) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMul, mulVec, dotProduct, Formalism.UG.cT, map_sum, map_mul, mul_comm]

theorem iso_eq (σ : k →+* k) (u u' : Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) :
    ∑ i, (u ᵥ* X) i * σ ((u' ᵥ* Y) i) = u ⬝ᵥ ((X * Formalism.UG.cT σ Y) *ᵥ (fun l => σ (u' l))) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conj_vecMul]

end Field

end PositivityTheory.Rg.Sw.Glob.Gen2H

namespace PositivityTheory.Rg.Sw.Glob

open Gen2H

theorem locRedField : LocRedField := by
  intro k _ σ hσ n g hg
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  set C := Gs.toBlocks₂₁ with hC
  set D := Gs.toBlocks₂₂ with hD
  have hrel : C * Formalism.UG.cT σ D = D * Formalism.UG.cT σ C := lower_rel σ g hg
  have hiso : ∀ u u' : Fin n → k,
      ∑ i, (u ᵥ* C) i * σ ((u' ᵥ* D) i) = ∑ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) := by
    intro u u'
    rw [iso_eq, iso_eq, hrel]
  let Surj : Finset (Fin n) → Prop := fun I => ∀ t : Fin n → k, ∃ u : Fin n → k, u ᵥ* D = 0 ∧ ∀ i ∈ I, (u ᵥ* C) i = t i
  have h0 : Surj ∅ := fun t => ⟨0, by simp, by simp⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter Surj) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have hSI : Surj I := (Finset.mem_filter.1 hI).2
  have hInj : ∀ u : Fin n → k, u ᵥ* D = 0 → (∀ i ∈ I, (u ᵥ* C) i = 0) → u ᵥ* C = 0 := by
    intro u hu hI0
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, (u ᵥ* C) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hjI : j ∉ I := fun h => hj (hI0 j h)
    have hS : Surj (insert j I) := by
      intro t
      obtain ⟨u', hu', ht⟩ := hSI t
      refine ⟨u' + ((t j - (u' ᵥ* C) j) / (u ᵥ* C) j) • u, ?_, ?_⟩
      · rw [add_vecMul, smul_vecMul, hu', hu, smul_zero, add_zero]
      · intro i hi
        rw [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · field_simp
          ring
        · rw [ht i hi, hI0 i hi, mul_zero, add_zero]
    have := hmax (insert j I) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)
    rw [Finset.card_insert_of_notMem hjI] at this
    omega
  refine ⟨I, ?_⟩
  rw [wIm, block_lower_right_mul_block_matrix, ← hGs, ← hC, ← hD, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hmix : ∀ j, (j ∈ I → (u ᵥ* C) j = 0) ∧ (j ∉ I → (u ᵥ* D) j = 0) := by
    intro j
    have := congrFun hu j
    rw [vecMul_mix] at this
    by_cases h : j ∈ I
    · rw [if_pos h] at this
      exact ⟨fun _ => this, fun h' => absurd h h'⟩
    · rw [if_neg h] at this
      exact ⟨fun h' => absurd h' h, fun _ => this⟩
  have hD0 : u ᵥ* D = 0 := by
    funext j
    by_cases hj : j ∈ I
    · obtain ⟨u', hu', ht⟩ := hSI (fun i => if i = j then 1 else 0)
      have h := hiso u u'
      rw [hu'] at h
      simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero] at h
      have hterm : ∀ i, (u ᵥ* D) i * σ ((u' ᵥ* C) i) = if i = j then (u ᵥ* D) j else 0 := by
        intro i
        by_cases hi : i ∈ I
        · rw [ht i hi]
          by_cases hij : i = j
          · subst hij
            simp
          · simp [hij]
        · have hne : i ≠ j := fun e => hi (e ▸ hj)
          rw [(hmix i).2 hi]
          simp [hne]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq'] at h
      simpa using h.symm
    · exact (hmix j).2 hj
  have hC0 : u ᵥ* C = 0 := hInj u hD0 (fun i hi => (hmix i).1 hi)
  exact hu0 (lower_inj g u hC0 hD0)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussF
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem cocycleZ : CocycleZ := by
  intro n e p q y y' Z hZ
  have hg := inG_mR y'
  have hnonzero {v : Fin n → ℂ} (hv : v ≠ 0) : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) ≠ 0 := by
    intro hz
    have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
    rw [smul_mulVec, dotProduct_smul, hz, smul_zero] at hpos
    exact (lt_irrefl (0 : ℂ)) hpos
  have hden (X : Matrix (Fin n) (Fin n) ℂ) :
      ¬ IsUnit ((mR y').toBlocks₂₁ * X + (mR y').toBlocks₂₂).det →
        ∃ v : Fin n → ℂ, v ≠ 0 ∧ star v ⬝ᵥ ((Xᴴ - X) *ᵥ v) = 0 := by
    rw [isUnit_iff_ne_zero, not_not]
    intro hdet
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨v, hv, ?_⟩
    rw [← identG hg X X, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero,
      dotProduct_sub, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have hD : IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂).det := by
    by_contra h
    obtain ⟨v, hv, hz⟩ := hden Z h
    apply hnonzero hv
    rw [← neg_sub, neg_mulVec, dotProduct_neg, hz, neg_zero]
  have hDh : IsUnit ((mR y').toBlocks₂₁ * Zᴴ + (mR y').toBlocks₂₂).det := by
    by_contra h
    obtain ⟨v, hv, hz⟩ := hden Zᴴ h
    exact hnonzero hv (by simpa only [conjTranspose_conjTranspose] using hz)
  have hW : IsSiegel (actZ y' Z) := by
    have hid := identG hg Z Z
    unfold IsSiegel actZ
    unfold IsSiegel at hZ
    set N := (mR y').toBlocks₁₁ * Z + (mR y').toBlocks₁₂
    set M := (mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂
    have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hD
    have hMM' : ∀ X : Matrix (Fin n) (Fin n) ℂ, (M⁻¹)ᴴ * (Mᴴ * X) = X := by
      intro X
      rw [← Matrix.mul_assoc, ← conjTranspose_mul, hMM, conjTranspose_one, Matrix.one_mul]
    have hZZ : Mᴴ * N - Nᴴ * M = Z - Zᴴ := by
      rw [← neg_sub, hid, neg_sub]
    have key : -(Complex.I / 2) • (N * M⁻¹ - (N * M⁻¹)ᴴ) =
        (M⁻¹)ᴴ * (-(Complex.I / 2) • (Z - Zᴴ)) * M⁻¹ := by
      rw [← hZZ, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc, hMM, Matrix.mul_one, hMM']
    rw [key]
    exact hZ.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hD)))
  have e1 : actZ y' Z * (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Z + toBlocks₁₂ (mR y') := by
    unfold actZ
    exact Matrix.nonsing_inv_mul_cancel_right _ _ hD
  have e2 : (actZ y' Z)ᴴ * (toBlocks₂₁ (mR y') * Zᴴ + toBlocks₂₂ (mR y')) =
      toBlocks₁₁ (mR y') * Zᴴ + toBlocks₁₂ (mR y') := by
    have hid := identG hg Z Zᴴ
    rw [sub_self] at hid
    have hDstar : IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂)ᴴ.det := by
      rw [det_conjTranspose]
      exact hD.star
    unfold actZ
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, sub_eq_zero.mp hid,
      nonsing_inv_mul_cancel_left _ _ hDstar]
  obtain ⟨n1, n2⟩ := num_den_mul (mR y) (mR y') Z _ e1
  obtain ⟨-, n3⟩ := num_den_mul (mR y) (mR y') Zᴴ _ e2
  refine ⟨hD, hDh, hW, ?_, ?_⟩
  · show ((mR (y * y')).toBlocks₁₁ * Z + (mR (y * y')).toBlocks₁₂) *
        ((mR (y * y')).toBlocks₂₁ * Z + (mR (y * y')).toBlocks₂₂)⁻¹ = actZ y (actZ y' Z)
    rw [mR_mul, n1, n2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (toBlocks₂₁ (mR y') * Z + toBlocks₂₂ (mR y')),
      Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]
    rfl
  · simp only [jF]
    rw [mR_mul, n2, n3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow, mul_zpow]
    ring

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem actZ_K {k : GR n} (hk : InK (mR k)) : actZ k (Complex.I • 1) = Complex.I • 1 := by
  obtain ⟨hC, hD⟩ := inK_blocks hk
  have hI : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold IsSiegel
    have hs : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
      rw [Complex.star_def, Complex.conj_I]
      linear_combination (-1 : ℂ) * Complex.I_sq
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul, hs, one_smul]
    exact Matrix.PosDef.one
  have hu := (cocycleZ n 0 0 0 k k _ hI).1
  have key : toBlocks₁₁ (mR k) * (Complex.I • 1) + toBlocks₁₂ (mR k) =
      (Complex.I • 1) * (toBlocks₂₁ (mR k) * (Complex.I • 1) + toBlocks₂₂ (mR k)) := by
    rw [hC, hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_add, smul_neg,
      smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
    abel
  unfold actZ
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

def mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, hG⟩

theorem mR_mkGR (M : M2 n) (hM : M.det ≠ 0) (hG : InG M) : mR (mkGR M hM hG) = M := rfl

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb]

theorem inG_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mM a) := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold InG mM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  simp [nU]

theorem det_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : (mM a).det ≠ 0 := by
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  unfold mM
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (ha.mul (Matrix.isUnit_nonsing_inv_det _ ha')).ne_zero

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocA
section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def bf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem bf_mul (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M * N) = bf M * bf N := by
  unfold bf; exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem block_matrix_to_fromBlocks (a b c d : Matrix (Fin n) (Fin n) R) : bf (GlobalTheory.StdUnn.blk4 a b c d) = fromBlocks a b c d := by
  unfold bf GlobalTheory.StdUnn.blk4; simp [Matrix.submatrix_submatrix]

theorem blkDm_eq (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blkDm M = (bf M).toBlocks₂₂ := rfl

theorem bf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M.map f) = (bf M).map f := rfl

theorem bf_one : bf (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := Matrix.submatrix_one_equiv _

theorem bf_injective : Function.Injective (bf : Matrix (Fin (n + n)) (Fin (n + n)) R → _) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [bf] using this

theorem block_matrix_one : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 :=
  bf_injective (by rw [block_matrix_to_fromBlocks, bf_one, fromBlocks_one])

theorem blkDm_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : (blkDm M).map f = blkDm (M.map f) := rfl

theorem det_map (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) : f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (GlobalTheory.StdUnn.blk4 a b c d).map f = GlobalTheory.StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  bf_injective (by rw [bf_map, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, fromBlocks_map])

theorem eI_map (f : R →+* S) (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R).map f = eI I := by
  ext i j; simp only [eI, map_apply, diagonal_apply]; split_ifs <;> simp

theorem wIm_map (f : R →+* S) (I : Finset (Fin n)) : (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R).map f = wIm I := by
  unfold wIm; rw [block_matrix_map]; simp [Matrix.map_sub, Matrix.map_one, Matrix.map_neg, eI_map]

theorem standard_symplectic_matrix_map (f : R →+* S) : (J2 R n).map f = J2 S n := by
  unfold J2; rw [block_matrix_map]; simp [Matrix.map_one, Matrix.map_neg]

theorem cT_map (σ : R →+* R) (σ' : S →+* S) (f : R →+* S) (hf : ∀ x, f (σ x) = σ' (f x)) {m p : Type}
    (M : Matrix m p R) : (Formalism.UG.cT σ M).map f = Formalism.UG.cT σ' (M.map f) := by
  ext i j; simp [Formalism.UG.cT, hf]

theorem isUnit_of (σ : R →+* R) (𝔪 : Ideal R) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (z : R) (h1 : z ∉ 𝔪) (h2 : σ z ∉ 𝔪) : IsUnit z := by
  by_contra hz
  obtain ⟨𝔫, h𝔫, hz𝔫⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hz' : z ∈ 𝔫 := hz𝔫 (Ideal.subset_span rfl)
  rcases horb 𝔫 h𝔫 with rfl | rfl
  · exact h1 hz'
  · exact h2 hz'

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

