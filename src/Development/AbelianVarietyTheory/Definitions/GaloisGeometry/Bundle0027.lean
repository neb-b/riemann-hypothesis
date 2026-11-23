module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0007
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
section
noncomputable section

namespace GlobalTheory.NFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem residualIrreducibility_forms_equivalent (D : D7) : SumRepresentations.adm6 D ↔ ResidualIrreducibleRankR D := Iff.rfl

end GlobalTheory.NFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnitaryRealisationReadingOfIdempotentActsViaLeve
section
noncomputable section

namespace GlobalTheory.NRows.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

section Read
variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
  (X : GlobalTheory.NJoin.RealAt D cf nch tp)

end Read

theorem unitaryRealisationReading_of_idempotent_acts_via_levelGroup {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (h : ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
      (l : (X.R.cV j).W →ₗ[ℂ] ℂ),
      Formalism.IndefR.Links.gaL (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) X.R.eG
        (Formalism.IndefR.Links.RealDat.eC (A := X.A) (Formalism.IndefR.Links.sg0 D X.A)) (fun g => l (X.fn hμ j f g)) =
        fun g => l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g)) : GoodIdempotentReadsAsGoodTypeProjector X := by
  intro μ hμ j f y hy
  unfold GlobalTheory.DownLift.GoodVt
  rw [hy]
  constructor
  · intro hf l
    rw [h μ hμ j f l, hf]
  · intro hg
    apply (X.IL.jMt μ hμ j).injective
    apply Subtype.ext
    funext g
    have key : ∀ l : (X.R.cV j).W →ₗ[ℂ] ℂ,
        l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g - X.fn hμ j f g) = 0 := fun l => by
      rw [map_sub, sub_eq_zero]
      exact congrFun ((h μ hμ j f l).symm.trans (hg l)) g
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (V := (X.R.cV j).W) _).1 key)

end GlobalTheory.NRows.Model

end
end

