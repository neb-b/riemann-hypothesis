module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AlgWtDualEx

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

theorem exists_place : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 L⁺)) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField L⁺)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  exact ⟨⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩⟩

instance nontrivial_AFplus : Nontrivial (AFplus L) := by
  obtain ⟨v⟩ := exists_place L
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (evalAt L v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

instance nontrivial_AL : Nontrivial (AL L) :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
    (algebraMap (L⁺) (AFplus L)).injective

end PI.UnitaryGroupMassFormula.AlgWtDualEx
