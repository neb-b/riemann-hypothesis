module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridgeSum
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
public import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
public import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IntermediateField IsDedekindDomain IdeleGroup FiniteSubfield GroundTheory.ProfCoh GroundTheory.LocalField

noncomputable section

section Transport

variable {K : Type*} [Field K] [NumberField K] {L L' : Type*} [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L'] [IsGalois K L] [IsGalois K L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K] L')]

theorem ideleSymbol_apply_algEquiv (e : L ≃ₐ[K] L') (x : IdeleGroup K) (l : L) :
    ideleSymbol K L' x (e l) = e (ideleSymbol K L x l) := by
  let _ : Algebra L L' := e.toRingHom.toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have h := AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l
  rw [restrictNormal_ideleSymbol L L' x] at h
  exact h.symm

end Transport

section Bridge

variable {K : FiniteSubfield} (E : FiniteSubfield) [hKE : Fact (K ≤ E)]

variable [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal

end Bridge

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

section Symbols

variable (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal galCommGroup

end Symbols

end

end GroundTheory.Global
