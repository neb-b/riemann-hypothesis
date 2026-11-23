module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfHL
section
namespace PI.LevelKSplit.W.Top6

theorem levelSplitting_of_heisenberg_levi (hH : PI.LevelKSplit.W.NC.HeisPAll) (hL : PI.LevelKSplit.W.NC.LevPAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.NC.levelSAll_of_semiNHS_heis_lev PI.LevelKSplit.W.SemiT.semidirect_topological_all hH hL
    PI.LevelKSplit.W.MVA.modulus_all_extensions PI.LevelKSplit.W.NCA.normal_conjugation_all

end PI.LevelKSplit.W.Top6
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviPartAll
section
noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

theorem levi_part_all : LevPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro hJ hinv r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp hinv hJ hP
  exact ⟨Asub (Af F) σ J P, levG hinv hJ hP, Asub_le, isClosed_Asub hJ hinv P T hP,
    continuous_levG hinv hJ P T hP,
    fun n hn => ⟨levG_mem hinv hJ hP n, levG_inv_mul hinv hJ hP n hn⟩,
    fun u hu hu1 => levi_inf_unipotent_eq_one hinv hJ hP u hu hu1,
    fun n hn m hm => unipotent_radical_normal n m hn hm,
    fun h hh u hu => H_comm_A H h u hh hu⟩

end PI.LevelKSplit.W.NCL
end
end

