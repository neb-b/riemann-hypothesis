module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryInertOddPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ValOfNotMem

@[expose] public section

theorem UpperTheory.Gal.Spc.specTopG :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecTopG := by
  intro hW E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq X
  obtain ⟨r, W, hrX, haux⟩ := UpperTheory.Gal.Spc.auxiliary_prime_holds E A n p S x U w₀ Up V hgen X
  refine ⟨r, haux.prime, hrX, haux.ne, ?_⟩
  intro N hrN hst J g θ hseen
  obtain ⟨L, hw, Ty, hTy⟩ := UpperTheory.Gal.Spc.tyEx E A n p S F x U w₀ Up V hoff r W haux N hrN hst
  have hx : UpperTheory.Gal.Spc.Extra S F.j := by
    rw [F.j_tr]
    exact ⟨fun w hp => UpperTheory.Gal.Spc.plTr E A n p S F.tr w hp,
      fun q hq' hqp g hg => UpperTheory.Gal.Spc.regTr E A n p S F.tr q hq' hqp g hg⟩
  exact UpperTheory.Gal.Spc.specData hW E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst
    L hw Ty hTy hx J g θ hseen
