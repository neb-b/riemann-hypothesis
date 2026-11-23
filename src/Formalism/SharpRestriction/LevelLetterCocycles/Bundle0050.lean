module

public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerZeroEqQ
public import Formalism.SharpRestriction.LevelLetterCocycles.SingleMemSpan
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0039

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelZeroMembershipOfHorizontal
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))

variable [IsDomain O] [NeZero n] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem level_zero_membership_of_horizontal (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB)
    (E1 : Formalism.MainNotions.UnusedSlot80.LevE.ExpFrame0 W levB) (E2 : Formalism.MainNotions.UnusedSlot80.LevE.ExpNoNeg0 W levB)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hζex : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (e : ℕ) :
    Formalism.MainNotions.UnusedSlot80.LevC.LevelZeroModP (W := W) A c' e T b sol := by
  intro x k f _ hr hfr hx
  obtain ⟨ζ, hζ⟩ := hζex
  choose u hu hfu using hfr
  exact Formalism.MainNotions.UnusedSlot80.CrD.secIn_of_fil W C A hA c' hc' T hT b hb.1 e ζ hζ f u hu hfu
    (fil_of_rep W levB C Ti E1 E2 h4 A hA c' hc' T hT b sol hb e ζ hζ x k f u hfu hr hx)

end Formalism.MainNotions.UnusedSlot80.CrC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneratorsOfUnits
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem univGenCore_of_lev [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W) (hS : PsStable W)
    (hRAT : CutU.RATCore W)
    (hInv : ∀ (A : ArcP n) (c : ZMod n), c ∈ A.cuts → ∀ s < A.len c, InvLevAt W s) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  univGenCore_of' W hinj hO2 hpu hR hKL hS hRAT hInv (finLev_of W hR (p_ne_zero_O' W) hpu)

theorem universal_generators_of_units [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) :
    Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → PsStable W → W.π₀ ∈ W.AΔ →
      CutU.RATCore W → CutU.InvLevCore W → Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  fun hR hKL hS _ hRAT hInv =>
    univGenCore_of_lev W hinj hO2 hpu hR hKL hS hRAT fun _ _ _ s _ => invLevAt_of W hInv s

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

