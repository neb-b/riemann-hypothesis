module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsTorRange
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualQOfTopInj
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualDOfDualQ
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsLimitOfCauchyAdicFiltration
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.T2SpaceOfLatticeNhdsBasis
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.MemOfMkMemRange
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.LocalBoundOfAllInputs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0001
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem le_of_growth {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have hq0 : 0 < q := by omega
  have h1 := h C
  have h2 : q ^ (C * (b + 1)) ≤ q ^ (C * a) :=
    Nat.pow_le_pow_right hq0 (Nat.mul_le_mul_left _ hba)
  have h3 : q ^ (C * b) * q ^ C ≤ q ^ (C * b) * C := by
    calc q ^ (C * b) * q ^ C = q ^ (C * (b + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ C * q ^ (C * b) := h2.trans h1
      _ = q ^ (C * b) * C := by ring
  have h4 : q ^ C ≤ C := Nat.le_of_mul_le_mul_left h3 (pow_pos hq0 _)
  have h5 : C < q ^ C := Nat.lt_pow_self (by omega)
  omega

theorem growth_le {q a h h' n m C C' : ℕ} (hq : 2 ≤ q)
    (H : ∀ r : ℕ, ∃ x x' y : ℕ, x ≤ C * q ^ (r * h) ∧ x' ≤ C' * q ^ (r * h') ∧ q ^ (r * a) ≤ y ∧
      y = x * x' * q ^ (r * n * m)) : a ≤ h + h' + n * m := by
  refine le_of_growth (C := C * C') hq fun r => ?_
  obtain ⟨x, x', y, hx, hx', hy, e⟩ := H r
  rw [Nat.mul_assoc r] at e
  calc q ^ (r * a) ≤ y := hy
    _ = x * x' * q ^ (r * (n * m)) := e
    _ ≤ (C * q ^ (r * h)) * (C' * q ^ (r * h')) * q ^ (r * (n * m)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hx')
    _ = C * C' * q ^ (r * (h + h' + n * m)) := by
        rw [Nat.mul_add, Nat.mul_add, pow_add, pow_add]; ring

theorem stable_pow {G : Type} [Group G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  have h := Submodule.mem_map_of_mem (f := actT L g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h


end PositivityTheory.LocalTateOrthogonality.Bk
