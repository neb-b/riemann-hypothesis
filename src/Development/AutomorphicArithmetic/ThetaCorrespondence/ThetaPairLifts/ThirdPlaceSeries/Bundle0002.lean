module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.ModularityOfHyps
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes
section
set_option synthInstance.maxHeartbeats 200000

section
open Module
noncomputable section
namespace Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module IsDiscreteValuationRing
section Hecke
open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)
end Hecke
section Record
open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br
variable {D : D7}
end Record
section Reduce
open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths
variable {D : D7}
def CongruenceAtTypePrimes' (CT : ℕ) (Q : ∀ (i : D.nd.Loc), Fin 2 →
    (D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) → ℕ → Prop) : Prop :=
  ∀ (i : D.nd.Loc) (k k' : Fin 2), k ≠ k' → D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GoodR D.nd i r → (∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) →
  ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s →
    Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) →
    CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k →
    SignOK i sg → HostJ i r eta s S sg U → (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i ρ π) →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    Q i k ρ eta
end Reduce
end Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModularityOfHyps
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.Published.CharCrysModel
theorem of_hypotheses_m_alt (hD : HeckeLAdicCharacterDeRham) (hB : DeRhamPotSemistable) (hW : AlgebraicCharacterWD)
    (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) : HeckeLAdicCharacterCrystalline := of_three hD hB hW
end GlobalTheory.Published.CharCrysModel
end
end
end

