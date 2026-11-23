module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff

@[expose] public section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.VF : Type := D.VQ

instance Datum.acgVF : AddCommGroup D.VF := inferInstanceAs (AddCommGroup D.VQ)

instance Datum.modQVF : Module ℚ D.VF := inferInstanceAs (Module ℚ D.VQ)

instance Datum.modFVF : Module D.F D.VF :=
  Module.compHom D.VQ ((D.endO.val : D.endO →ₐ[ℚ] Module.End ℚ D.VQ).toRingHom.comp D.actF.toRingHom)

theorem Datum.smul_VF (x : D.F) (v : D.VF) :
    x • v = (((D.actF x : D.endO) : Module.End ℚ D.VQ) (v : D.VQ) : D.VF) := rfl

instance Datum.towerVF : IsScalarTower ℚ D.F D.VF :=
  ⟨fun q x v => by
    show ((D.actF (q • x) : D.endO) : Module.End ℚ D.VQ) v = q • ((D.actF x : D.endO) : Module.End ℚ D.VQ) v
    rw [map_smul]; rfl⟩

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem Datum.finrank_VF : Module.finrank D.F D.VF = D.m * D.n := by
  have h1 : Module.finrank ℚ D.VF = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa; haveI := D.finLa
    show Module.finrank ℚ (ℚ ⊗[ℤ] D.La) = _
    rw [Module.finrank_baseChange, D.rankLa]
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  haveI : FiniteDimensional D.F D.VF := Module.Finite.of_restrictScalars_finite ℚ D.F D.VF
  rw [← Module.finrank_mul_finrank ℚ D.F D.VF, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MatUnit

open Module

variable {L U R : Type} [Field L] [AddCommGroup U] [Module L U] [Ring R] {m : ℕ}
  (σ : Matrix (Fin m) (Fin m) R →+* Module.End L U)

variable {A : Type} [Ring A] (α : A →+* Module.End L U)

end GlobalTheory.UPel.HT.MatUnit

section Main

open NumberField Matrix

end Main
