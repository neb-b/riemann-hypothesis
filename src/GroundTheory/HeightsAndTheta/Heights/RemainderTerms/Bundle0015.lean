module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurEvalMatrix
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSchurEvalMatrix.aeval_completeSymmetric (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by
  unfold completeSymmetric
  by_cases h0 : 0 ≤ d
  · rw [if_pos h0, h1 N k d.toNat hk hkN]
    have hdiv : (k ∣ d.toNat) ↔ ((k : ℤ) ∣ d) := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h0]
    by_cases hd : (k : ℤ) ∣ d
    · rw [if_pos (hdiv.mpr hd), if_pos ⟨h0, hd⟩]
    · rw [if_neg (fun h => hd (hdiv.mp h)), if_neg (fun h => hd h.2)]
  · rw [if_neg h0, map_zero, if_neg (fun h => h0 h.1)]

theorem SchSchurEvalMatrix.proof (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem hsymm_isHomogeneous (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    (hsymm σ ℚ n).IsHomogeneous n := by
  rw [Schur.hsymm_eq_sum_finsuppAntidiag]
  refine IsHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : ∑ i, l i = n := (mem_finsuppAntidiag.mp hl).1
  rw [← hsum]
  exact IsHomogeneous.prod _ _ _ fun i _ => by
    simpa using (isHomogeneous_X ℚ i).pow (l i)

theorem SchSchurHomogeneous.proof : SchSchurHomogeneous.Statement := by
  intro σ _ _ r lam
  unfold schur
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun π _ => ?_
  rw [Units.smul_def]
  have hmem : (∏ i, (Matrix.of fun i j : Fin r =>
      completeSymmetric σ ((lam i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))) (π i) i) ∈
      homogeneousSubmodule σ ℚ (∑ i, lam i) := by
    rw [mem_homogeneousSubmodule]
    by_cases h : ∀ i, 0 ≤ (lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)
    · have hdeg : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat = ∑ i, lam i := by
        have h1 : ((∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
            ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h i)
        have h2 : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) = ∑ i, (lam i : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Equiv.sum_comp π (fun i => (lam i : ℤ)), Equiv.sum_comp π (fun i => ((i : ℕ) : ℤ))]
          ring
        exact_mod_cast h1.trans h2
      rw [← hdeg]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      simp only [Matrix.of_apply, completeSymmetric, if_pos (h i)]
      exact hsymm_isHomogeneous σ _
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [completeSymmetric, not_le.mpr hi])]
      exact isHomogeneous_zero _ _ _
  exact zsmul_mem hmem _

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurRowsToK
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchSchurRowsToK.proof : SchSchurRowsToK.Statement := by
  intro σ _ _ r k nu hanti hsum
  by_cases hrk : r ≤ k
  · exact (Schur.schur_padPartition σ nu k hrk).symm
  · replace hrk : k < r := Nat.lt_of_not_le hrk
    have hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 1 ≤ nu i := Nat.one_le_iff_ne_zero.mpr hne
      have h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j :=
        Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))
      have h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1
      omega
    have heq : nu = Schur.padPartition r
        (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0) := by
      funext i
      simp only [Schur.padPartition]
      by_cases hik : (i : ℕ) < k
      · simp [hik, i.isLt]
      · simp only [hik, dite_false]
        exact hzero i (by omega)
    calc schur σ nu
        = schur σ (Schur.padPartition r
            (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)) :=
          congrArg (schur σ) heq
      _ = _ := Schur.schur_padPartition σ _ r hrk.le

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSmallBlockProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSmallBlockProduct.sum_fin_staircase (r : ℕ) : ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r,
    Finset.sum_range_reflect (fun i => i) r, Finset.sum_range_id]

theorem SchSmallBlockProduct.vandermondeOf_X_comp {m : ℕ} {κ : Type*} (g : Fin m → κ) :
    vandermondeOf (fun i => (X (g i) : MvPolynomial κ ℚ)) =
      rename g (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) := by
  simp [vandermondeOf, map_prod, map_sub, rename_X]

theorem SchSmallBlockProduct.vandermondeOf_X_eq_alternant (m : ℕ) :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun j : Fin m => m - 1 - (j : ℕ)) := by
  rw [← Schur.det_pow_staircase_eq_vandermondeOf, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant {m : ℕ} (lam : Fin m → ℕ) :
    schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun i : Fin m => lam i + (m - 1 - (i : ℕ))) := by
  rw [← Schur.det_pow_add_staircase_eq, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.proof (h1 : SchAevalSignedRename.Statement)
    (h2 : SchAlternantHomogeneous.Statement) : SchSmallBlockProduct.Statement := by
  intro r a c lam
  set e : Fin r → ℕ := fun i => lam i + (r - 1 - (i : ℕ)) with he
  have hy : yRoot 1 r a c 0 = fun i => C c.sign * (X (yIndex 1 r a c 0 i) : RootRing 1 (r + a)) :=
    rfl
  have hz : zRoot 1 r a c 0 = fun i => (X (zIndex 1 r a c 0 i) : RootRing 1 (r + a)) := rfl

  have hVy : vandermondeOf (yRoot 1 r a c 0) =
      aeval (yRoot 1 r a c 0) (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))) := by
    simp [vandermondeOf, map_prod, map_sub]

  have hdeg : ∑ i, e i = ∑ i, lam i + r * (r - 1) / 2 := by
    rw [he, Finset.sum_add_distrib, SchSmallBlockProduct.sum_fin_staircase]
  have hA : aeval (yRoot 1 r a c 0) (alternant e) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) * rename (yIndex 1 r a c 0) (alternant e) := by
    rw [hy, ← hdeg]
    exact h1 (Fin r) (Fin 1 × Fin (r + a)) c.sign (yIndex 1 r a c 0) _ (alternant e) (h2 (Fin r) e)
  have hVz : vandermondeOf (zRoot 1 r a c 0) =
      rename (zIndex 1 r a c 0) (alternant fun j : Fin a => a - 1 - (j : ℕ)) := by
    rw [hz, SchSmallBlockProduct.vandermondeOf_X_comp, SchSmallBlockProduct.vandermondeOf_X_eq_alternant]
  have hplace_l : smallBlockPlace r a c ∘ Sum.inl = yIndex 1 r a c 0 := rfl
  have hplace_r : smallBlockPlace r a c ∘ Sum.inr = zIndex 1 r a c 0 := rfl
  rw [hVy, ← map_mul, SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant, hA, hVz, map_mul, rename_rename,
    rename_rename, hplace_l, hplace_r, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchStrictAntiSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchStrictAntiSplit.add_gap_le {r : ℕ} {d : Fin r → ℕ} (hd : StrictAnti d) :
    ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → d j + k ≤ d i :=
  _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd

theorem SchStrictAntiSplit.sum_staircase (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r,
    Finset.sum_range_id]

theorem SchStrictAntiSplit.proof : SchStrictAntiSplit.Statement := by
  intro r n d hd hsum
  have hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i := by
    intro i
    have hr : 0 < r := Fin.pos i
    have h := SchStrictAntiSplit.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩
      (by simp; omega)
    omega
  refine ⟨hlow, ?_⟩
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, ?_⟩
  · have hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) =
        ∑ i : Fin r, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)
    rw [SchStrictAntiSplit.sum_staircase] at hadd
    omega
  · intro i j hij
    have h := SchStrictAntiSplit.add_gap_le hd ((j : ℕ) - i) i j (by omega)
    have := hlow i
    have := hlow j
    have : (i : ℕ) ≤ j := hij
    have : (j : ℕ) < r := j.isLt
    show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))
    omega

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchWeightedPreimage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchWeightedPreimage.proof (h1 : SchPowerSumHomWeighted.Statement) :
    SchWeightedPreimage.Statement := by
  classical
  intro N k P hsym hhom
  obtain ⟨S₀, hS₀⟩ := Flag.exists_powerSumHom_eq hsym
  let w : Fin N → ℕ := fun i => (i : ℕ) + 1
  refine ⟨weightedHomogeneousComponent w k S₀, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous k S₀⟩
  have hfin := weightedHomogeneousComponent_finsupp (w := w) S₀
  have hsum := sum_weightedHomogeneousComponent w S₀
  rw [finsum_eq_sum _ hfin] at hsum
  have hterm : ∀ m : ℕ, homogeneousComponent k (powerSumHom N (weightedHomogeneousComponent w m S₀))
      = if k = m then powerSumHom N (weightedHomogeneousComponent w m S₀) else 0 :=
    fun m => homogeneousComponent_of_mem
      (h1 N m _ (weightedHomogeneousComponent_isWeightedHomogeneous m S₀))
  have key : homogeneousComponent k (powerSumHom N S₀) =
      powerSumHom N (weightedHomogeneousComponent w k S₀) := by
    conv_lhs => rw [← hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [hterm, Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have hk0 : weightedHomogeneousComponent w k S₀ = 0 := by
        by_contra hne
        exact hk (Set.Finite.mem_toFinset (hs := hfin) |>.mpr hne)
      rw [hk0, map_zero]
  rw [← key, hS₀, homogeneousComponent_eq_self hhom]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurPowerSumCoefficient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchurPowerSumCoefficient.proof (h1 : SchWeightedPreimage.Statement)
    (h2 : SchEvalPowerSumHom.Statement) (h3 : SchSchurHomogeneous.Statement)
    (h4 : SchSchurAtRootsOfUnity.Statement) : SchurPowerSumCoefficient.Statement := by
  intro N r k hk1 hkN nu hanti hsum
  have hhom := h3 (Fin N) r nu
  rw [hsum] at hhom
  obtain ⟨S, hS, hw⟩ := h1 N k (schur (Fin N) nu) (Schur.schur_isSymmetric (σ := Fin N) nu) hhom
  refine ⟨S, hS, ?_⟩
  have e1 := h2 N k hk1 hkN S hw
  rw [hS, h4 N r k nu hk1 hkN hanti hsum] at e1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply Rat.cast_injective (α := ℂ)
  split_ifs with h
  · rw [if_pos h] at e1
    push_cast
    rw [eq_div_iff hk]
    linear_combination -e1
  · rw [if_neg h] at e1
    push_cast
    rcases mul_eq_zero.mp e1.symm with h0 | h0
    · exact absurd h0 hk
    · exact h0

end

end GroundTheory.Heights₂.Heights.RestTerms
end

