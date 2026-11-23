module

public import Formalism.PeriodIntegrals.Bundle0011

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Lattice
section
namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem isTorsionFree_alg (O : Type) [CommRing O] [IsDomain O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O A := by
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • a = r • b := hab
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap O K r ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hr0
  have h1 : (algebraMap O K r) • a = (algebraMap O K r) • b := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hab'
  calc a = ((algebraMap O K r)⁻¹ * algebraMap O K r) • a := by rw [inv_mul_cancel₀ hK, one_smul]
    _ = ((algebraMap O K r)⁻¹ * algebraMap O K r) • b := by rw [mul_smul, h1, ← mul_smul]
    _ = b := by rw [inv_mul_cancel₀ hK, one_smul]

theorem isTorsionFree_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O ↥(As O A) := by
  obtain ⟨h⟩ := isTorsionFree_alg O K A
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • (a : A) = r • (b : A) := by
    have h2 := congrArg (fun x : ↥(As O A) => (x : A)) hab
    simpa using h2
  exact Subtype.ext (h hr hab')

theorem free_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A]
    [Module.Finite O ↥(As O A)] : Module.Free O ↥(As O A) := by
  haveI := isTorsionFree_as O K A
  exact Module.free_of_finite_type_torsion_free'

theorem isLocalizedModule_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A] :
    IsLocalizedModule (nonZeroDivisors O) ((As O A).val.toLinearMap) := by
  obtain ⟨htf⟩ := isTorsionFree_alg O K A
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro s
    have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp only [Module.algebraMap_end_apply] at hxy
      exact htf (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero s.2)) hxy
    · intro y
      refine ⟨(algebraMap O K s)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    have hy : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
    have hyO : IsAlgebraic O y := (IsFractionRing.isAlgebraic_iff O K A).mpr hy
    obtain ⟨c, hc0, hc⟩ := hyO.exists_integral_multiple
    refine ⟨(⟨c • y, hc⟩, ⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩), ?_⟩
    rfl
  · intro x₁ x₂ h
    exact ⟨1, by rw [Subtype.ext h]⟩

theorem finrank_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    [Module.Finite O ↥(As O A)] : Module.finrank O ↥(As O A) = Module.finrank K A := by
  haveI : Module.Free O ↥(As O A) := free_as O K A
  haveI := isLocalizedModule_as O K A
  let b := Module.Free.chooseBasis O ↥(As O A)
  let b' := b.ofIsLocalizedModule K (nonZeroDivisors O) ((As O A).val.toLinearMap)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end PI.UnitaryGroupMassFormula.EfRankSum
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Points
section
namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

theorem mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ζ.asIdeal ∈ (maximalIdeal O).primesOver ↥(As O A) := by
  haveI := ζ.isMaximal
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) ζ.asIdeal)).symm

theorem isMaximal_of_mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] {q : Ideal ↥(As O A)}
    (hq : q ∈ (maximalIdeal O).primesOver ↥(As O A)) : q.IsMaximal := by
  obtain ⟨hp, hl⟩ := hq
  have h : q.under O = maximalIdeal O := hl.over.symm
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) q
    (h ▸ IsLocalRing.maximalIdeal.isMaximal O)

noncomputable def ptsEquiv (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] :
    Pts O A ≃ (maximalIdeal O).primesOver ↥(As O A) where
  toFun ζ := ⟨ζ.asIdeal, mem_primesOver O A ζ⟩
  invFun q := ⟨q.1, isMaximal_of_mem_primesOver O A q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ptsEquiv_apply (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ((ptsEquiv O A ζ : (maximalIdeal O).primesOver ↥(As O A)) : Ideal ↥(As O A)) = ζ.asIdeal := rfl

theorem finite_pts (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] : Finite (Pts O A) := by
  classical
  haveI : Finite ((maximalIdeal O).primesOver ↥(As O A)) := by
    have hfin : ((maximalIdeal O).primesOver ↥(As O A)).Finite :=
      Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)
    exact hfin.to_subtype
  exact Finite.of_equiv _ (ptsEquiv O A).symm

end PI.UnitaryGroupMassFormula.EfRankSum
end

