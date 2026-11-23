module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory.Published

def FlathTensorProduct : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∃ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H),
          IsFactorisation σ J (fun v => (R v).π) ξ π B

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
section
noncomputable section

open scoped ComplexConjugate NNReal ENNReal
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp GlobalTheory.MixModel
open GlobalTheory.Mem.Th (InfF CptF)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause DoublingIso)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP.Model

variable {D : D7} {A B : HSp D}

theorem vol_pos (mH : Measure (GA D B)) [mH.IsHaarMeasure] : 0 < (autMeasure B mH).real Set.univ :=
  ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 (NeZero.ne _)) (measure_ne_top _ _)

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)}

end GlobalTheory.RallisIP.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory.Published

def UnitaryIrreducibleAdmissible : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F))
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GLoc σ J v →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∀ K : Subgroup (GLoc σ J v), IsOpen (K : Set (GLoc σ J v)) → IsCompact (K : Set (GLoc σ J v)) →
          FiniteDimensional ℂ (fixed (toRep π) K)

end GlobalTheory.Published

end
end

