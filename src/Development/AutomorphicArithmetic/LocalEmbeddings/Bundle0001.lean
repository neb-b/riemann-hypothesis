module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

variable {D : D7} {v : Pl D.host.F}

def evW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Lev.EAf D →+* Fv D.host.F v :=
  (complEquiv τ (splitPrime_under τ)).symm.toRingHom.comp (cpt (D := D) (splitPrime τ))

theorem complEquiv_evW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    complEquiv τ (splitPrime_under τ) (evW τ z) = cpt (D := D) (splitPrime τ) z := by
  exact (complEquiv τ (splitPrime_under τ)).apply_symm_apply _

theorem evW_toEAf (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) : evW τ (toEAf D a) = piW τ a := by
  apply (complEquiv τ (splitPrime_under τ)).injective
  rw [complEquiv_evW]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [FlipMatch.cpt_tmul, FlipMatch.piW_tmul, map_mul, complEquiv_apply, complEquiv_apply,
      complMap_apply_emb, mul_comm]
    congr 1
    rw [← FlipMatch.complMap_apply_under (splitPrime_under τ)]
    rfl
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end GlobalTheory.BotMatch

end
end

-- bundled from Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.Grid GlobalTheory.ChainFr
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinMatch

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def HalfEl (P : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (t₀ : ∀ v : P, E →ₐ[F] Fv F v) (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : Prop :=
  (∀ u : AF F, (∀ v ∈ P, GlobalTheory.AdelicU.evFin F v u = 0) → u • z = 0) ∧ ∀ v : P, piW (t₀ v) z = 0

end Generic

variable {D : D7}

def piF {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) : EAf D →+* Fv D.host.F v :=
  (Algebra.TensorProduct.lift t (evalV D.host.F v) fun _ _ => Commute.all _ _).toRingHom

theorem piF_toEAf {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : AE D) :
    piF t (toEAf D z) = piW t z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => exact mul_comm _ _

structure IsPair (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (M : Model D.sp.cm.sig Vs Ws) : Prop where

  base : Bs.IsGood D.sp.cm.sig

  psi : Bs.ψ = ψ

  JV : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram

  JW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  herm : ∃ r s, Vs.IsHerm D.sp.cm.sig Bs r s

  skew : ∃ r s, Ws.IsSkew D.sp.cm.sig Bs r s

  good : M.IsGood Bs.ψ

def IsLat {S X : HSp D} {d : ℕ} (e : Fin d ≃ Fin X.rank) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)) : Prop :=
  (∀ y, y ∈ Vs.L ↔ star y ∈ ΛS) ∧ ∀ y, y ∈ Ws.L ↔ (fun k => y (e.symm k)) ∈ GlobalTheory.SkewLat.scLat D.host.AA ΛX

def IsCart (ε : Bool) {S X : HSp D} (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin d ≃ Fin X.rank) (Bs : Base D.host.F D.host.E)
    (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d) : Prop :=
  ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
    Ws.θ w = ((B.cart τ).submatrix e e).map conj

end GlobalTheory.FinMatch

end
end

