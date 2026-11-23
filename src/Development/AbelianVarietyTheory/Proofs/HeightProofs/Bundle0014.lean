module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.Divisibility.WeightFamilies

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelic_lattice_iff_local_selfDual_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (V : HSpace E) (y : Fin V.rank → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0} ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  first | exact @GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | exact GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | (intros; apply GlobalTheory.LatticeLocalGlobal.mem_latHat_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeOfSqLeFMulR
section
noncomputable section

namespace GlobalTheory.ConstCompare

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7}

theorem choose_two_add (p q : ℕ) :
    p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q).choose 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ← ih]
    simp only [Nat.choose_one_right]
    ring

end GlobalTheory.ConstCompare

end
end

