module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.DifferentiableConjConj
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusCoordinates
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

noncomputable section

namespace GlobalTheory.EtaPinnedCompare

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.I2 (TorusAt Vsp Hf PT)
open scoped ComplexConjugate

section Pins

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem theta_entire {W : UnfAt U k x} (Wu : UnitAt W) : Differentiable ℂ Wu.θ := by
  have hF : GlobalTheory.EtaAn.AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have key : ∀ y (_ : y = W.F.u (W.ik k) W.Pm) (s : Semi.LB.Sec (PPx y)),
      GlobalTheory.EtaAn.IsFnOf W.F (W.ik k) W.Pm Wu.fr y s Wu.θ → Differentiable ℂ Wu.θ := by
    intro y hy s hs
    subst hy
    exact (GlobalTheory.EtaAn.isFnOf_entire_factor E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF s Wu.θ hs).1
  exact key _ W.pt (U.un k x).s Wu.c7

end Pins

section Bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Z : FD.Data E r} {x : FD.Frame Z.Ψ r}

end Bound

section Record

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D}

end Record

end GlobalTheory.EtaPinnedCompare
