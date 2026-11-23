module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def HodgeTateDatumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∀ [Algebra ℤ_[p] R] (P : Out.PolAV (Spec (CommRingCat.of R))),
    Nonempty (TorsRep P.A p) ∧
    ∃ (cp : R) (_ : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
      (H : HodgeTateDatum p P.g v R ℤ_[p] AlgEquiv.refl cp) (pt : Nb p P.g → (sp (R₀ := R) R ⟶ P.A)),
      IsTorsPts P.A p pt ∧ ∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

def SubquotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∀ (N : Type) [AddCommGroup N] (M : Submodule R (N → C)), IsAbFactor p M →
    ∀ K : AddSubgroup N, GenAF p M K

def OrdinaryCurveStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : R)}) R →
  ∃ (A : Over (Spec (CommRingCat.of R))) (_ : GrpObj A) (L : LB A.left), IsAbelianScheme A ∧ L.IsLB ∧
    Out.RelAmple A L ∧ ∃ (T : TorsRep A p) (pt : ZMod p × ZMod p → (sp (R₀ := R) R ⟶ A)),
      IsTorsPts A p pt ∧ torsFun C T pt =
        tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
          (intFun R (ZMod p))

end GlobalTheory.CompanionTheory.Ar.GR
end
end

