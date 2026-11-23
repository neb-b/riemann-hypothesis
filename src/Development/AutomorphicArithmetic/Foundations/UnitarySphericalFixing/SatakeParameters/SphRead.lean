module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0742
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M.Sph

theorem exists_satAt_of_sphAtG : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, SphAtG π v → ∃ α, NG.SatAt π Dv α :=
  fun L _ _ _ n π v w h Dv hs => _root_.GlobalTheory.SatInertEx.exists_satAt L n π v w h Dv hs.1

theorem exists_satAt_of_overPl_sphAtG : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → SphAtG π v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α :=
  fun L _ _ _ n π v w h hs => _root_.GlobalTheory.SatExists.exists_satAt L n π v w h hs.1

theorem exists_satAt_of_dict : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → SphAtG π v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α :=
  fun L _ _ _ n F π U hD v w h hs => _root_.GlobalTheory.SatExist.exists_satAt L n F π U hD v w h hs.1

theorem satAgree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (SphAtG π v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' :=
  fun L _ _ _ n F π U hD v w h => ⟨fun hs => (_root_.GlobalTheory.InertDict.satake_agree L n F π U hD v w h).1 hs.1, (_root_.GlobalTheory.InertDict.satake_agree L n F π U hD v w h).2⟩

theorem isSph {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) (hs : SphAtG π s.v) :
    GlobalTheory.SmGL.IsSpherical σ.ρ := GlobalTheory.SphLoc.isSpherical_of_sphAt π s σ hσ hs.1

end UpperTheory.One.M.Sph
