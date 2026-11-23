module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025

@[expose] public section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

theorem exists_multilinear_gen {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P (d + 1)) :
    ∃ F : MultilinearMap (RingHom.id ℤ) (fun _ : Fin d => K → ℤ) ℤ,
      ∀ bs, F bs = NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) bs := by
  have hX : IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) d := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  let I := P.map (MvPolynomial.map (Int.castRingHom ℚ))
  have hadd (bs : Fin d → K → ℤ) (i : Fin d) (x y : K → ℤ) :
      NumbersDVR.intNum ℚ I (Function.update bs i (x + y)) =
        NumbersDVR.intNum ℚ I (Function.update bs i x) +
          NumbersDVR.intNum ℚ I (Function.update bs i y) :=
    FieldNumbers.IntNumAdd.full ℚ K ι I hXN.multiHomog hXN.relevant d hd bs i x y
  refine ⟨{ toFun := NumbersDVR.intNum ℚ I
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun _ => rfl⟩
  · intro inst bs i x y
    obtain rfl : inst = instDecidableEqFin d := Subsingleton.elim _ _
    exact hadd bs i x y
  · intro inst bs i c x
    obtain rfl : inst = instDecidableEqFin d := Subsingleton.elim _ _
    let g : (K → ℤ) →+ ℤ := AddMonoidHom.mk'
      (fun y => NumbersDVR.intNum ℚ I (Function.update bs i y)) (hadd bs i)
    exact map_zsmul g c x

end SheetDecomposition
