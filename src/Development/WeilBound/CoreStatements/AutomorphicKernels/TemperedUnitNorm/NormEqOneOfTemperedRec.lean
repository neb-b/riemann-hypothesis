module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import ReciprocityTheory.GaloisValuations.Global
public import GroundTheory.PAdicHodge.AInfGalois

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TempSatGal

theorem comp_complexConj {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (τ : E →+* Qbar l) :
    ι.toRingHom.comp (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
      ComplexEmbedding.conjugate (ι.toRingHom.comp τ) := by
  refine RingHom.ext fun x => ?_
  have := IsCMField.complexEmbedding_complexConj (K := E) (ι.toRingHom.comp τ) x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact this

theorem sum_map_affine (M : Multiset ℂ) (u v : ℂ) :
    (M.map fun z => u + v * z).sum = (M.card : ℂ) * u + v * M.sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons, Multiset.sum_cons]
    push_cast; ring

end GlobalTheory.TempSatGal
