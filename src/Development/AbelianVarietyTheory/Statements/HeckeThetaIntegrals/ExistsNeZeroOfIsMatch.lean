module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
public import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareSt.Model

variable {D : D7}

theorem exists_isWeil (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (M X : HSp D) {χ χ' : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χ) (h2 : IsHeckeChar D χ') (r1 : ResEta D χ M.rank)
    (r2 : ResEta D χ' X.rank) : ∃ ω, IsWeil ψ ε M X χ χ' ω := by
  obtain ⟨ω', hω'⟩ := hW D ψ (sgn ε M) X χ χ' hψ h1 h2 r1 r2
  refine ⟨ω'.comp ((ofSgn ε M).symm.toMonoidHom.prodMap (MonoidHom.id (GA D X))), ?_⟩
  have e : GlobalTheory.Grid.WRep.toSgn (S := M) (T := X) ε
      (ω'.comp ((ofSgn ε M).symm.toMonoidHom.prodMap (MonoidHom.id (GA D X)))) = ω' := by
    ext x : 1
    rcases x with ⟨g, k⟩
    simp [GlobalTheory.Grid.WRep.toSgn]
  unfold GlobalTheory.Grid.IsWeil
  rw [e]
  exact hω'

private theorem isHeckeChar_div' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · rw [div_eq_mul_inv]
    exact h.1.mul h'.1.inv
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem exists_weil_of_isTriple (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {W W₁ X : HSp D} {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β) :
    (∃ ωA, IsWeil ψ true W X β (β / α) ωA) ∧ ∃ ωB, IsWeil ψ false W₁ X α (α / β) ωB := by
  refine ⟨exists_isWeil hW hψ true W X h.hecB (isHeckeChar_div' h.hecB h.hecA) h.resB ?_,
    exists_isWeil hW hψ false W₁ X h.hecA (isHeckeChar_div' h.hecA h.hecB) h.resA ?_⟩
  · rw [div_eq_mul_inv, h.rank]
    exact Formalism.L2.Theta.resEta_mul h.resB (Formalism.L2.Theta.resEta_inv h.resA)
  · rw [div_eq_mul_inv, h.rank, add_comm]
    exact Formalism.L2.Theta.resEta_mul h.resA (Formalism.L2.Theta.resEta_inv h.resB)

end GlobalTheory.SquareSt.Model

end
