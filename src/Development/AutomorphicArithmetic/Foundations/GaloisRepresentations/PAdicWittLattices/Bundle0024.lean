module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0022
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
public import Development.EtaleCohomology.WeilConjectures.Bundle0001
public import Development.EtaleCohomology.WeilConjectures.Bundle0003
public import Development.EtaleCohomology.EtaleDuality.FinAdicFin

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JVBcS
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jVBcS :
    VBcS := by
  intro l _ k Ω _ _ _ _ φ hl X p _ _ n i
  refine GlobalTheory.GenusTwoPureComparison.Cmp.pullHQ_bijective l _ n i fun m => ?_
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ m : ℕ) : k) := by
    push_cast
    exact hl.pow m
  exact GlobalTheory.GenusTwoPureComparison.Cmp.eqv_fieldChange UpperTheory.Et.proper_base_change UpperTheory.Et.etale_base_change_of_duality (l ^ m) k Ω φ hq p i n
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.VFinHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.G3

theorem vFin_holds : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hT : ∀ a m, Finite (Ht (l ^ a) (sch.obj X) m i) := fun a m => by
    have : NeZero (l ^ a) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact UpperTheory.Et.etale_finiteness_of_duality (l ^ a) k (by rw [Nat.cast_pow]; exact hl.pow a) p m i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l _ n i (fun a => hT a n)
      (LateralTheory.EWeil.AdicKerPf.AdicKer_of GlobalTheory.EtC.RedCoef.a11 l _ i
        (fun b => LateralTheory.Fin.AdicFin.etale_bockstein_sequence_adic_finiteness GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 l b _ i
          (LateralTheory.EWeil.FinQCut.inv_of_over hl p)) hT n)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.G3

end
end

