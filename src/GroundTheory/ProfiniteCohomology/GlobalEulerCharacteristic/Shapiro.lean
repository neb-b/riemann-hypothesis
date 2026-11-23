module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroRatio
public import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyTransfer

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

theorem exists_gsEulerRatio_coind_eq :
    ∃ ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion,
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
        [IsDiscreteRep B] [Finite B],
        gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
            ιr =
          @gsEulerRatio L (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B)
            (IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL).symm) B) ιrL := by
  choose mem hmem using realMemberPlace_surjective S ιr hL
  choose ιrL e he using fun w => exists_real_data_of_eq S ιr hL (mem w) w
    ((coe_realMemberPlace S ιr hL (mem w)).symm.trans (congrArg Subtype.val (hmem w)))
  exact ⟨ιrL, fun B _ _ => gsEulerRatio_coind_eq_of S hL ιr B ιrL mem hmem e he⟩

end

end GroundTheory.ProfCoh
