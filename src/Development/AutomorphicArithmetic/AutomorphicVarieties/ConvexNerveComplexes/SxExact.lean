module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002

@[expose] public section

open NumberField UpperTheory.V

theorem UpperTheory.V.ConeExtensionAcyclic.sx_exact (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (KT.Sx L N) (KT.Sx.face L N) m :=
  have h := ConeExtensionAcyclic.acyc_simp (KT.good L N)
  KT.faceexact _ _ h.1 h.2.1 h.2.2 m
