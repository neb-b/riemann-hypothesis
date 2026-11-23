module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0003
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
public import Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0393
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0944
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
section
section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]

def IsClassMapD {LP : Type*} (dim : LP → ℕ) (rc : ∀ n, QRep g n → LP) : Prop :=
  ∀ n (π : QRep g n), IrrSm π → dim (rc n π) = n ∧ ∀ π' : QRep g n, IrrSm π' → fixK1 π'.ρ ≠ ⊥ → (rc n π = rc n π' ↔ Nonempty (π ≅ π'))

end GlobalTheory.SerSys
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M

end UpperTheory.One.M
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end DiscreteGroups.sglob.DzType.Rt
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.LabPin
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.New.field {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (_hL : RecTExists) {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {rc' : IrrGL (k := w'.adicCompletion E') → WD h'} (H : IsRecT h rc) (H' : IsRecT h' rc') : UpperTheory.One.M.FieldG rc rc' :=
  UpperTheory.One.M.fieldGT E Ω A w h E' Ω' A' w' h' rc rc' H H'
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.IsQgOfOver
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.isQg_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have key : Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb w (D.host.g k) hw) := by
    refine GlobalTheory.TypeRec.Model.emb_surjective _ _ _ (fun h => ?_)
      (by
        simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
          (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw))
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime k).ne_zero
    have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
    have := hs w.asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h)
    exact w.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  exact ⟨_, this, RingEquiv.ofBijective _ ⟨RingHom.injective _, key⟩, Formalism.BasicNotions.Examples₂.LocF.emb_cont _ _ hw⟩

end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroLoc

end GlobalTheory.DepthZeroLoc
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame

end GlobalTheory.DepthZeroTame
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise
namespace GlobalTheory.DepthZeroType

end GlobalTheory.DepthZeroType
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove

noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000

def New.nMv (_ : TrivialCondition) {D : D7} (m : Mv D) (n : NTiedGPlaceholder D) : NTiedGPlaceholder m.D :=
  @NTiedGPlaceholder.mk _

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PairLiftH
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.SplitPairLift

namespace UpperTheory.One.M

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def RepGood {T : WDTie N A} (S : Reading T) : Prop := ∀ i w hw P, GoodI ((S i w hw).rep P)

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.One.M

theorem noSplit (D : D7) (w : PlE D.host) (v) (hw : ¬ IsSplitPl D.host w) (hv : NG.OverPl w v) : NoSplit D.host.E v := by
  intro s hs
  by_cases e : s.w = w
  · exact hw (e ▸ GlobalTheory.SplitPlaceConj.isSplitPl_w D s)
  · refine not_isSplitAt D w hw ⟨s.w, e, HeightOneSpectrum.ext ?_⟩
    exact s.w_under.trans ((congrArg HeightOneSpectrum.asIdeal hs).trans hv.symm)

end UpperTheory.One.M
end
end

