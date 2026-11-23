module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymDecomposition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem antisymmetrize_finset_sum (f N : ℕ) {ι : Type*} (s : Finset ι) (g : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, g i) = ∑ i ∈ s, antisymmetrize f N (g i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antisymmetrize, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

theorem FlagAntisymDecomposition.proof (h1 : FlagSymmetricMulAntisym.Statement)
    (h2 : FlagPowerSumSymmetric.Statement) : FlagAntisymDecomposition.Statement := by
  intro f N F G Q R hF hR
  rw [hF, Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_left_comm, h1 f N _ _ (h2 f N l σ), hR, mul_left_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagCoeffBlockPermute
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

def blockPermuteEquiv (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    Fin f × Fin N ≃ Fin f × Fin N where
  toFun p := (p.1, w p.1 p.2)
  invFun p := (p.1, (w p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem FlagCoeffBlockPermute.proof : FlagCoeffBlockPermute.Statement := by
  intro f N w P α
  classical
  set E := blockPermuteEquiv f N w with hE
  set β : Fin f × Fin N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2) with hβ
  have hmap : Finsupp.mapDomain E β = α := by
    ext q
    obtain ⟨p, rfl⟩ := E.surjective q
    rw [Finsupp.mapDomain_apply_of_injective E.injective]
    simp [hβ, hE, blockPermuteEquiv]
  have hren : blockPermute f N w P = rename E P := rfl
  rw [hren, ← hmap, coeff_rename_mapDomain E E.injective]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffNotDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDiffNotDvd.proof : FlagDiffNotDvd.Statement := by
  intro σ _ a b c d hab hcd h1 h2 hdvd
  let ψ : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
    aeval (fun i => X (if i = a then b else i))
  have hψ : ∀ i, ψ (X i) = X (if i = a then b else i) := fun i => by
    simp only [ψ, aeval_X]
  obtain ⟨q, hq⟩ := hdvd
  have h := congrArg ψ hq
  rw [map_mul, map_sub, map_sub, hψ, hψ, hψ, hψ, if_pos rfl, if_neg (Ne.symm hab), sub_self,
    zero_mul, sub_eq_zero] at h
  have hcd' := X_injective h
  by_cases hc : c = a <;> by_cases hd : d = a
  · exact hcd (hc.trans hd.symm)
  · rw [if_pos hc, if_neg hd] at hcd'
    exact h1 ⟨hc.symm, hcd'⟩
  · rw [if_neg hc, if_pos hd] at hcd'
    exact h2 ⟨hd.symm, hcd'.symm⟩
  · rw [if_neg hc, if_neg hd] at hcd'
    exact hcd hcd'

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

namespace FlagDiffPrime

variable {σ : Type} [DecidableEq σ]

def collapse (a b : σ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun i => if i = a then X b else X i

theorem collapse_X_sub (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by
  simp [collapse]

theorem dvd_sub_collapse (a b : σ) (Q : MvPolynomial σ ℚ) :
    (X a - X b : MvPolynomial σ ℚ) ∣ Q - collapse a b Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [collapse]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have e : p * X i - collapse a b p * collapse a b (X i) =
        (p - collapse a b p) * X i + collapse a b p * (X i - collapse a b (X i)) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    by_cases h : i = a
    · rw [h]; simp [collapse]
    · simp [collapse, h]

theorem collapse_eq_zero_of_dvd (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, collapse_X_sub, zero_mul]

theorem dvd_of_collapse_eq_zero (a b : σ) {P : MvPolynomial σ ℚ}
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by
  simpa [h] using dvd_sub_collapse a b P

theorem proof : FlagDiffPrime.Statement := by
  intro σ _ a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_ne_zero]
    exact fun h => hab (X_injective h)
  · intro hu
    have hu' := hu.map (collapse a b)
    rw [collapse_X_sub] at hu'
    exact not_isUnit_zero hu'
  · intro A B h
    have h0 := collapse_eq_zero_of_dvd a b h
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Or.inl (dvd_of_collapse_eq_zero a b h0)
    · exact Or.inr (dvd_of_collapse_eq_zero a b h0)

end FlagDiffPrime

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDividedDifferencePoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagDividedDifferencePoly.proof (h1 : FlagVandermondeDvd.Statement) :
    FlagDividedDifferencePoly.Statement := by
  intro f N H
  obtain ⟨R, hR⟩ := h1 f N _ (isBlockAlternating_antisymmetrize f N H)
  refine ⟨R, hR, fun w => ?_⟩
  have h := isBlockAlternating_antisymmetrize f N H w
  rw [hR, map_mul, Flag.blockPermute_blockVandermonde, smul_mul_assoc] at h
  have hs : blockSign f N w ≠ 0 := by
    intro h0
    have := Flag.blockSign_mul_self f N w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ (Flag.blockVandermonde_ne_zero f N) (smul_right_injective _ hs h)

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagHomogeneousComponentMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagHomogeneousComponentMul.proof : FlagHomogeneousComponentMul.Statement := by
  intro σ P G k n hP
  exact HomogeneousComponentMul.proof σ ℚ P G k n hP

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagInjSumBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem FlagInjSumBound.finset_sum_bound (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    have hsub : S' ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hcard : S'.card ≤ m := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    refine ⟨by omega, fun heq => ?_⟩
    have hmeq : m = S'.card := by omega
    have hS' := ih₂ (by omega)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_range.2 (by omega)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))

theorem FlagInjSumBound.proof : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  set S := Finset.univ.image g with hSdef
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, g i = ∑ x ∈ S, x := by
    rw [hSdef, Finset.sum_image (fun i _ j _ h => hg h)]
  obtain ⟨h₁, h₂⟩ := FlagInjSumBound.finset_sum_bound S
  rw [hcard, Finset.sum_range_id] at h₁ h₂
  rw [hsum]
  refine ⟨h₁, fun heq i => ?_⟩
  have hi : g i ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ i)
  exact Finset.mem_range.1 (h₂ heq hi)

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem flagIntegral_sum_smul_blockPermute (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Flag.flagIntegral_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Flag.flagIntegral_add, ih, smul_eq_C_mul,
      Flag.flagIntegral_C_mul]

theorem FlagIntegralAntisymmetrize.proof (h1 : FlagIntegralPermute.Statement) :
    FlagIntegralAntisymmetrize.Statement := by
  intro f N H
  rw [antisymmetrize, flagIntegral_sum_smul_blockPermute]
  rw [Finset.sum_congr rfl fun w _ => by
    rw [h1 f N w H, ← mul_assoc, Flag.blockSign_mul_self, one_mul]]
  rw [Finset.sum_const, Finset.card_univ, Flag.card_blockPerm, nsmul_eq_mul]
  push_cast
  ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralPermute.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagIntegralPermute.Statement := by
  classical
  intro f N w H
  let e : Fin f × Fin N ≃ Fin f × Fin N := Equiv.prodShear (Equiv.refl _) w
  have hcomp : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) =
        Finsupp.equivMapDomain e.symm α := by
    intro α; ext p; simp [Finsupp.equivMapDomain_apply, e, Equiv.prodShear]
  have hH : ∀ α, AddMonoidAlgebra.coeff (blockPermute f N w H) α = AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) := by
    intro α; rw [h1, hcomp]
  have hD : ∀ α, AddMonoidAlgebra.coeff (blockVandermonde f N) (Finsupp.equivMapDomain e.symm α) =
      blockSign f N w * AddMonoidAlgebra.coeff (blockVandermonde f N) α := by
    intro α
    rw [← hcomp, ← h1, Flag.blockPermute_blockVandermonde, coeff_smul, smul_eq_mul]
  have hs2 : blockSign f N w * blockSign f N w = 1 := Flag.blockSign_mul_self f N w
  have hs0 : blockSign f N w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs2; exact zero_ne_one hs2
  have hfac : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivMapDomain e.symm α).prod (fun _ n => (n.factorial : ℚ)) =
        α.prod (fun _ n => (n.factorial : ℚ)) := by
    intro α; rw [Finsupp.prod_equivMapDomain]
  unfold flagIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
  · simp only [MvPolynomial.mem_support_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      Finsupp.domCongr_apply, hD]
    exact ⟨fun h => mul_ne_zero hs0 h, fun h h' => h (by rw [h', mul_zero])⟩
  · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, hH, hD, hfac]
    linear_combination (-(AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) *
      AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ n => (n.factorial : ℚ)))) * hs2

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralTopComponent.proof (h1 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralTopComponent.Statement := by
  intro f N Φ
  unfold flagIntegral
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : α.degree = topDegree f N := by
    rw [Finsupp.degree_eq_weight_one]
    exact h1 f N (mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent, if_pos hdeg]

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem FlagIntegralTopDegree.proof (h1 : FlagAltTopDegree.Statement)
    (h2 : FlagAntisymHomogeneous.Statement) (h3 : FlagIntegralViaQuotient.Statement) :
    FlagIntegralTopDegree.Statement := by
  intro f N H hH
  obtain ⟨e, he⟩ := h1 f N (antisymmetrize f N H) (isBlockAlternating_antisymmetrize f N H)
    (h2 f N H _ hH)
  have hI := h3 f N H (C e) (by rw [he, mul_comm])
  rw [constantCoeff_C] at hI
  have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)))).mpr
      (Flag.blockVandermonde_ne_zero f N)
  have hdd : dividedDifference f N H = algebraMap ℚ (FractionRing (RootRing f N)) e := by
    rw [dividedDifference, he, map_mul, mul_div_assoc, div_self hΔ, mul_one,
      IsScalarTower.algebraMap_apply ℚ (RootRing f N) (FractionRing (RootRing f N)),
      MvPolynomial.algebraMap_eq]
  rw [hdd, ← map_mul, hI]

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondeMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralVandermondeMul.proof (h1 : FlagIntegralTopComponent.Statement)
    (h2 : FlagHomogeneousComponentMul.Statement) (h3 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralVandermondeMul.Statement := by
  intro f N R
  rw [h1 f N (blockVandermonde f N * R),
    h2 _ (blockVandermonde f N) R (topDegree f N) (topDegree f N) (h3 f N),
    if_pos le_rfl, Nat.sub_self, homogeneousComponent_zero, mul_comm,
    Flag.flagIntegral_C_mul, constantCoeff_eq]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

