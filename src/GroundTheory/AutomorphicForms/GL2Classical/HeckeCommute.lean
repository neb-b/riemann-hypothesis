module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2Classical.Adelic
public import GroundTheory.AutomorphicForms.GL2Classical.ConstantTerm
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle0002
public import GroundTheory.AutomorphicForms.Bundle0016
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle0001
public import GroundTheory.AutomorphicForms.HeckeAlgebraLevel

@[expose] public section

open NumberField IsDedekindDomain Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable (p q : ℕ) [NeZero p] [NeZero q]

instance : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩

variable [Fact p.Prime]

variable [Fact q.Prime] (N : ℕ) [NeZero N]

variable {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
