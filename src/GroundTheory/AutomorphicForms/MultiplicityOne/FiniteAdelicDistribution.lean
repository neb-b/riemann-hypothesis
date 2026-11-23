module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0017
public import GroundTheory.AutomorphicForms.AdelicGLn
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Filter Set

open scoped RestrictedProduct

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

def pullL {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    locallyConstantCompactSupport Y ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport X ℂ ℂ where
  toFun φ := ⟨(φ : Y → ℂ) ∘ e, mem_locallyConstantCompactSupport.2
    ⟨φ.2.1.comp_continuous e.continuous, φ.2.2.comp_homeomorph e⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

end

end Whittaker

end GroundTheory.Automorphic
