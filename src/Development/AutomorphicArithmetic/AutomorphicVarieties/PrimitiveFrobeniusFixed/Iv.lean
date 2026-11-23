module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.OverIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PsiOf

@[expose] public section

theorem UpperTheory.V.ML.iv :
    GlobalTheory.Published.PoitouTateDuality → ReciprocityTheory.Gal.UnramifiedOrthogonality → UpperTheory.V.Odd.PsiBound :=
  fun h₁ h₂ => UpperTheory.V.ML.psiOf (UpperTheory.V.ML.recip h₁ h₂)
