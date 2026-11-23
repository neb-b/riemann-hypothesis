module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredPlacesFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem CentredPlacesFinite.proof : CentredPlacesFinite.Statement := by
  intro L _ _ O hft _ m _
  have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
    @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
      (Ideal.Quotient.mkₐ_surjective ℤ m)
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hp, -⟩ :=
    @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
      (by convert hq <;> rfl) (ringChar (O ⧸ m))
      (ringChar.charP _)
  set p := ringChar (O ⧸ m)
  have hpm : (p : O) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (O ⧸ m) p
  have hp0 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_
  have hlt := (hw.2 (p : O)).mpr hpm
  have hcoe : ((p : O) : L) = (p : L) := by simp
  rw [hcoe] at hlt
  exact hlt.ne

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalNormalIndex.proof : LocalNormalIndex.Statement := by
  intro L _ _ O hft hfr m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors
  set C := integralClosure A L
  have : Algebra.FiniteType ℤ O := hft
  have : CharZero O := ⟨fun a b h ↦ by
    have := congrArg (fun t : O ↦ (t : L)) h
    simpa using this⟩

  have hfin : Module.Finite O (integralClosure O L) :=
    Model.finite_integralClosure_fractionRing_of_charZero O L
  obtain ⟨d, hd, hdI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O)
    (Module.Finite.iff_fg.mp hfin : (Subalgebra.toSubmodule (integralClosure O L)).FG)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap O L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

  have hdC : ∀ x ∈ C, algebraMap O L d * x ∈ A := by
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := O) (M := m.primeCompl) (Rₘ := A) x hx
    obtain ⟨o, ho⟩ := hdI _ hsx
    have hs0 : algebraMap O L s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m.primeCompl_le_nonZeroDivisors hs)
    simp only [Submonoid.smul_def, Algebra.smul_def] at ho
    refine ⟨o, s, hs, ?_⟩
    rw [ho]
    field_simp

  have hAC : A.toSubring ≤ C.toSubring := fun x hx ↦
    (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  set f := algebraMap O L d
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hdL
  have h1 : A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤
      C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) := AddSubgroup.map_mono hAC
  have h2 : C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toSubring.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdC y hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at e1
  have hcard : (A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex
      A.toSubring.toAddSubgroup ≠ 0 := by
    let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
    have hq1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) =
        Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A d : A.toSubring)}) := by
      refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact (e.commutes d).symm
    have hfL : ((algebraMap O A d : A.toSubring) : L) = f := rfl
    have hcq := card_quot_span_eq_relIndex A.toSubring (algebraMap O A d : A.toSubring)
    rw [hfL] at hcq
    have key : Nat.card (Localization.AtPrime m ⧸
        Ideal.span {algebraMap O (Localization.AtPrime m) d}) ≠ 0 := by
      rw [LocalQuotCard.proof L O hft hfr m d hd0]
      refine pow_ne_zero _ ?_
      have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
        @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
          (Ideal.Quotient.mkₐ_surjective ℤ m)
      let _ : Field (O ⧸ m) := Ideal.Quotient.field m
      obtain ⟨hp, hc⟩ :=
        @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
          (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)
      rw [hc]
      exact pow_ne_zero _ hp.ne_zero
    rw [← hcq]
    exact fun h ↦ key (hq1.trans h)
  rw [← e1] at hcard
  exact left_ne_zero_of_mul hcard

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitArchSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval_smul_of_isMultiHomog (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ)
    (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (c : ι → ℂ) (z : Coord n → ℂ) :
    eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  have key : ∀ f : MvPolynomial (Coord n) ℤ,
      eval c (Geo.mConeMap (ι := blockIdx n) z f) = eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f p hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [Geo.mConeMap, mul_comm]
  classical
  rw [← key, mConeMap_of_isMultiHomog z s a hs, eval_map]
  simp [map_prod, mul_comm]

end GroundTheory.Heights₂.Heights
end

