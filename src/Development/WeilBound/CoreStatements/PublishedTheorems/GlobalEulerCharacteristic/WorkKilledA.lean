module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Bundle0001
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Shapiro
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.CardCohomologyZeroMackeyRepOfNeTop
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ApplySubrepresentationCongr
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ToFunEqZeroOfForallIsCyclic
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_a

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable def resTo {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (K' : FiniteSubfield) [Fact (K ≤ K')]
    (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) :
    Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 ℚ̄ (placesOver S)) := by
  letI : IsScalarTower K.1 K'.1 ℚ̄ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Rep.res (gsBaseChange S hK').symm.toMulEquiv.toMonoidHom
    (Rep.res (gsOpenSubgroup S hK' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)

instance isDiscreteRep_resTo {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (K' : FiniteSubfield)
    [Fact (K ≤ K')] (hK' : ∀ x : K'.1, algebraMap K'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] :
    IsDiscreteRep (resTo S K' hK' M) := by
  unfold resTo
  have : IsScalarTower K.1 K'.1 ℚ̄ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isDiscreteRep_res_subtype M (gsOpenSubgroup S hK' : Subgroup _)
  exact IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom (gsBaseChange S hK').symm) _

end PositivityTheory.Lit1.GEN.W_killed_a
