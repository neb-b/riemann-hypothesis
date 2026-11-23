module

public import ReciprocityTheory.GaloisValuations.SymplecticRankFourModularity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace ReciprocityTheory.Hyp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def resGal (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] : G L Ω →* G K Ω :=
  AlgEquiv.restrictScalarsHom K

end ReciprocityTheory.Hyp
