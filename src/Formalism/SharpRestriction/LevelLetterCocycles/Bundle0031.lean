module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0028
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0029
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfLeafLemmas
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem local_theorem_of_leaf_lemmas (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep)
    (hUL : UnivLinkStep) (hR : InvLiftStep) (hC : ClassMapStep) (hH : FrameStep)
    (hMFL : ModelFLinkStep) (hP5 : ExpansionFormHypothesis) (hML : ModelLStep) (hMQL : ModelQLinkStep)
    (hU1L : FirstFrameOfModels) (hkp : KapPiStep) (hU2L : SecondPropositionOfRank) (hU2R : SecondRankHypothesis)
    (hD : DownSlotOfModels) (hUp : UpSlotOfModels) (hMx : MixedSlotOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC160 hFont hdr hrk hA
  have hMQ : ModelQStep := modelQStep_of hMQL hML
  have hU2 : SecondPropositionHypothesis := second_proposition_of_models hU2L hMQ hU2R hML
  have hMF := modelFStep_of hMFL hP5 D HW F Cm CA CB CK hdr hrk hA
  have hU1 := first_frame_of_models hU1L hML D HW F Cm CA CB CK hdr hrk hA hMF
  have hUniv : univR D HW :=
    hUL D HW F hA.2.2.2.2.1 hd (hR D HW F Cm CA CB CK hA) (hC D HW F Cm CA CB CK hA)
      (hH D HW F Cm CA CB CK hA) hMF hU1 (hkp D HW F Cm CA CB CK hA) (hU2 D HW F Cm CA CB CK hA)
      (hD D HW F Cm CA CB CK hA hMF) (hUp D HW F Cm CA CB CK hA hMF) (hMx D HW F Cm CA CB CK hA hdr hrk hMF)
  have hKill : killR D :=
    killR_of_steps D HW hd (hq D hA.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.1) (hn D)
      (h9 D HW F Cm hA.1)
      (splitR_of_steps D HW F hA.2.1 hA.2.2.2.2.1 (he D HW F Cm CA CB CK hA) (hw D HW F Cm CA CB CK hA)
        (hk D HW F Cm CA CB CK hA hFont) (hl D HW F Cm CA CB CK hA) (hg D HW F Cm CA CB CK hA)
        (hf D HW F Cm CA CB CK hA) (hγ D HW F Cm CA CB CK hA) (ho D HW F Cm CA CB CK hA))
      hUniv
  exact local_theorem_of_good_extensions D C hC160 (local_form_of_three_inputs D (hG D HW F Cm CA CB CK hA) (hL D HW F Cm CA CB CK hA) hKill)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G PowerSeries IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem ringSteps_of [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (η : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (hℓ2 : PD.p ≠ 2) (hℓm : (PD.p : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G1 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι X = (w : PowerSeries O) * X ^ (PD.p - 1))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ X = (1 + X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL, 1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL)
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a) :
    (lvModel Hy f' kind b η).K1b ∧ (lvModel Hy f' kind b η).HasU (W.χΓ W.gam) ∧
      (∀ s < ell, ((lvModel Hy f' kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s ∧
        ((lvModel Hy f' kind b η).lev s).PhiGammaCommute) ∧
      (lvModel Hy f' kind b η).UnitsAt ∧ (lvModel Hy f' kind b η).Compl ϖ := by
  obtain ⟨w, hw⟩ := G1
  exact LevelStatements.Link.linkRing LevelStatements.Lv.rhoUnique LevelStatements.Lv.splitCompl LevelStatements.Lv.cycloSimple
    LevelStatements.Lv.psCoprime LevelStatements.Lv.rhoUnit LevelStatements.Lv.descendDvd LevelStatements.Lv.piSeries ϖ hϖ
    (lvData Hy f' kind b η) (hℓ := ⟨PD.hp⟩) hℓ2 hℓm n0 hn0 hroot (baseIdOf hR).ι w hw W.φ₀ hφ
    (baseIdOf hR).ι_φ LevelStatements.Lv.psCyclo G2 (rhoZ W c) hρζ (lvModel Hy f' kind b η)
    (fun s _ a ζ => map_eval_rhoL hR c s a ζ) (W.χΓ W.gam) (uZ : ℤ_[PD.p]) huZ ιZ hutie
    (fun _ _ => rfl)
    (fun s _ f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)
    (fun j => (j.1 : ℤ_[PD.p]))
    (fun j => (by simpa using congrArg (fun x : ℤ_[PD.p]ˣ => (x : ℤ_[PD.p])) j.2 :
      ((j.1 : ℤ_[PD.p])) ^ (PD.p - 1) = 1))
    hom'
    (fun s _ j f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)


open Classical in
def SecondPropositionRingInput (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Prop :=
  IsUnit (algebraMap (LetA O n) W.EE π') ∧ IsUnit (algebraMap (LetA O n) W.EE Eπ) ∧
  (∃ g ∈ W.AΔ, W.γA W.gamK π' = π' * g) ∧
  ∃ ν ∈ W.AΔ, ν * W.γA W.gamK (Eπ ^ h') = Eπ ^ h' ∧
  ∃ (N : ℕ) (f : ℕ → LetA O n) (cc : ℕ → O),
    (∀ k, f k ∈ W.AΔ) ∧
    (letE c : LetA O n) * ∏ k ∈ Finset.range N, f k = (letE c : LetA O n) * (π' * Eπ ^ (2 * h')) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ (a₀ : O) (b : LetA O n), b ∈ W.AΔ ∧
      (letE c : LetA O n) * a = (letE c : LetA O n) * (algebraMap O (LetA O n) a₀ + f k * b)) ∧
    (∀ k < N, ∀ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      (letE c : LetA O n) * (ν * W.γA W.gamK ((∏ j ∈ Finset.range k, f j) * a) -
          algebraMap O (LetA O n) (cc k) * ((∏ j ∈ Finset.range k, f j) * a)) =
        (letE c : LetA O n) * ((∏ j ∈ Finset.range (k + 1), f j) * b)) ∧
    ((Finset.range N).filter fun k => cc k = 1).card ≤ finrank K₀ K + 1

end Local

def secondPropositionRingAll (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c, SecondPropositionRingInput ((HW l).W K 1 LL hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def SecondRingHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → secondPropositionRingAll D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfLiteratureExactness
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem ddExactL_of_litFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Split.DDExactL D HW := by
  intro l _ K LL hG hCA _ T₂ Y ι π _ _ hses
  obtain ⟨hinj, -, hker⟩ := (h l K LL hCA).2.1 T₂ Y _ ι π hses
  refine ⟨fun x => (hker _).2 ⟨x, rfl⟩, fun x hx => hinj (by rw [hx, map_zero]), fun u hu => (hker u).1 hu⟩

theorem splitting_of_literature_exactness (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hS : Split.SplitShapeL D HW) : SplittingArcLifting D HW F Cm :=
  splitting_general_of_exactness D HW F Cm hA h6 hH hTr hWX (ddExactL_of_litFont D HW F hFont) hS

end Formalism.MainNotions.UnusedSlot80
end
end

