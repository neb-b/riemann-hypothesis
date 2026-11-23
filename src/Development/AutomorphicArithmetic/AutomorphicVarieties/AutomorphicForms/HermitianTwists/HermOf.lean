module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

@[expose] public section

open UpperTheory.V UpperTheory.V.Af

open scoped BigOperators

theorem UpperTheory.V.Af.Rn.hermOf :
    UpperTheory.V.Af.Rn.HermOf := by
  intro c π hπ
  refine Br.hermEx ℚ 2 one_le_two π fun φ hφ => ?_
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1, LinearMap.add_apply]
  rw [(Br.capTwo ℚ π Rat.infinitePlace _ _ (hπ Rat.infinitePlace) φ hφ).1,
    add_neg_cancel, zero_smul]
