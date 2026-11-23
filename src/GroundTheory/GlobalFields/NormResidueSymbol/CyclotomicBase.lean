module

public import Mathlib
public import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
public import GroundTheory.GlobalFields.NormResidueSymbol.Rational
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0001

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

namespace CyclotomicSymbol

section Roots

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

end Roots

section Sub

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (M ≃ₐ[K] M)]

end Sub

section ClassSymbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) h

variable {L}

@[simp]
theorem ideleClassSymbol_mk (h : (diagonal K).range ≤ (ideleSymbol K L).ker) (x : IdeleGroup K) :
    ideleClassSymbol L h (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Continuous (ideleClassSymbol L h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

end ClassSymbol

universe u

end CyclotomicSymbol

end

end GroundTheory.Global
