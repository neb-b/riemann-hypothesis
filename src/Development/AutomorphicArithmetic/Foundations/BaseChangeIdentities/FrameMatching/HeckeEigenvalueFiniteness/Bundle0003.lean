module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Mok0
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IsHeckeFsum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.ExTbOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.FrameInertAll
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.EigInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.BcWeyl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.SumPairSignEqRho
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.FX
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem gcHecke : GcHecke := by
  intro E _ _ _ n w hw b ϖ c
  have hg : gc w b ϖ c = ∑ x ∈ c.support,
      (c x * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)) • fU n w b ϖ (lOf x) := by
    funext γ
    simp only [gc, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hg]
  exact isHecke_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ _ (GlobalTheory.LocFinU.continuous_cj w)

theorem frameEx_of_fin (hUS : USide) (hCF : CandFin) : FrameEx :=
  frameEx_of hUS (_root_.GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne GlobalTheory.CompanionTheory.LocHecke.locAlg) (_root_.GlobalTheory.CompanionTheory.SpecModel.specTrace _root_.GlobalTheory.CompanionTheory.UMod.uModel GlobalTheory.CompanionTheory.LocHecke.locAlg)
    GlobalTheory.CompanionTheory.LocHecke.locAlg (exTbOf Inert.frameInert_all.1 Inert.frameInert_all.2.1 inertInSec) Inert.frameInert_all.2.2.2.1
    Inert.frameInert_all.2.2.2.2.1 (coneEigOf eigInert LemB.bcWeyl) satCompAt candIndep hCF
    (fun _ _ _ _ _ _ _ _ _ _ F₀ => mok0 F₀) IndefiniteRowSideFullHecke.coneTwo' gcHecke
    (locC IndefiniteRowSideFullHecke.shufEx' IndefiniteRowSideFullHecke.vResStd' IndefiniteRowSideFullHecke.shufStd' targetAlg monoRes) locE muVal powEig

end UpperTheory.HeckeLevelFrameExistence

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.SameOfStrict
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem joins_fin (hSJ : StrictJoin)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (μ : HChar E) {ι : Type} [Finite ι] (a : ι → ℕ) (kA kB : ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - a i)) :
    ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i (Pa : Pre E (a i)) (Pb : Pre E (n - a i)) (D : Pre E n),
      IsJoin (μ ^ (n - a i)) (μ ^ a i) Pa Pb D → (∃ ja, Strict Pa (PA i ja)) → (∃ jb, Strict Pb (PB i jb)) →
      ∃ j, Strict D (Dl j) := by
  let J : Type := {x : Σ i, Fin (kA i) × Fin (kB i) // ∃ D : Pre E n, ∃ (Pa : Pre E (a x.1)) (Pb : Pre E (n - a x.1)),
    IsJoin (μ ^ (n - a x.1)) (μ ^ a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)}
  haveI : Finite J := Subtype.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  choose Df Paf Pbf hf using fun x : J => x.2
  refine ⟨k, fun j => Df (e.symm j), fun i Pa Pb D hj ⟨ja, ha⟩ ⟨jb, hb⟩ => ?_⟩
  let x : J := ⟨⟨i, ja, jb⟩, D, Pa, Pb, hj, ha, hb⟩
  refine ⟨e x, ?_⟩
  show Strict D (Df (e.symm (e x)))
  rw [e.symm_apply_apply]
  exact hSJ E n _ _ _ _ Pa (Paf x) Pb (Pbf x) D _ hj (hf x).1 (strict_common ha (hf x).2.1) (strict_common hb (hf x).2.2)

theorem same_of_strict (hSPr : StrictProd) (hII : IsoInv) (hAd : AdmProd)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w))
    (ho : IsOpen (K : Set (GLw n w))) (hle : K ≤ GlobalTheory.LFun.KGL w (n := n)) (D D' : Pre E n) (hs : Strict D D') :
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
      Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
      FiniteDimensional ℂ ↥(fixed (prodAt D' w) K) := by
  have h := hII (GLw n w) _ _ (prodAt D w) (prodAt D' w) (hSPr E n D D' hs w) K
  exact ⟨fun τ => h.1 τ.V τ.ρ, h.2.1, hAd E n D' w K ho hle⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

