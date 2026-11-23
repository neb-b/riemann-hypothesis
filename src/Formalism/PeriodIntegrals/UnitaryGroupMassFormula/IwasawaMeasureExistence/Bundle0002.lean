module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdeleRing

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd
section
noncomputable section

namespace PI.IwaMeasEx.Nrm

open NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open Formalism.MainNotions.S

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


end Gen

section Unit

open Formalism.L2.S.S7.GLOne

variable (I : AutInst)

abbrev iE : I.E →+* AEf I := Formalism.UG.inclE (F := I.F) (Af I.F)

end Unit

end PI.IwaMeasEx.Nrm

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq
section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

theorem mem_Bx {N : ℕ} (hN : 0 < N) {a : Af I.F} (ha : N • a ∈ Ohat I.F) : a ∈ Bx I N := by
  refine ⟨N • a, ha, ?_⟩
  have hN0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
  simp only
  rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, inv_mul_cancel₀ hN0,
    map_one, one_mul]

end Cpt

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

end Cpt

end PI.IwaMeasEx.Wau

end
end

