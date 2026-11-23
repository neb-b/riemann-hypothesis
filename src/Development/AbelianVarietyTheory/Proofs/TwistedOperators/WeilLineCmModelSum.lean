module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0294
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchCont

open scoped SchwartzMap

theorem lintegral_of_integral {l : Type} [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hi : ∀ u : GlobalTheory.RealWeil.Sch l, MeasureTheory.Integrable (fun x => ‖u x‖ ^ 2) MeasureTheory.volume := fun u =>
    (u.memLp 2 MeasureTheory.volume).integrable_norm_pow two_ne_zero
  have e : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2) := fun u => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hi u) (.of_forall fun x => by positivity)]
    congr 1
    funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, h]

end GlobalTheory.ArchCont

namespace GlobalTheory.ArchCont

open scoped SchwartzMap RealInnerProductSpace

end GlobalTheory.ArchCont

