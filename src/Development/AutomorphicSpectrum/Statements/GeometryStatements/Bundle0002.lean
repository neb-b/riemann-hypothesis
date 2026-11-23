module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeTateCokerSharp
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open TensorProduct GlobalTheory.PDivGroup

def HodgeTateCokerSharp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) →
      ∀ w : G.dual.omega, κ • w ∈ LinearMap.range (hodgeTateLinear G)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.LevelCoverSt
section
namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def LevelCoverSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (e : Y.X), e ∈ genericPoints Y.X →
    ∀ N : ℕ, 1 ≤ N → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x)
      (f : M.X ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (t : SAB H M.X) (_ : SABMap t Y.t f) (z : Ωˣ)
      (ev : D.La → (Over.mk M.ξ ⟶ t.G)),
      Flat.NormalCpt M.ξ ∧ IsFinite f ∧ f (GlobalTheory.CompanionTheory.Ar.genPt M.ξ) = e ∧ M.ξ ≫ f = y ≫ Y.j ∧ IsFullLevelAt D t M.ξ N z ev ∧
      FullTorsion t.G M.ξ N ∧ ∀ q : Cpt M.ξ, unitAt M.ξ q (z : Ω)

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

def TwistAut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : HostAut H), Nonempty (TwIso D g) ∧ ∀ a : TwIso D g, ∃ (h : TwOK Xo.univ g a) (Φ : Xo.X ≅ Xo.X),
      Φ.hom ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ.hom)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

def PropFTop : Prop :=
  PtsIntegrableStatement → MetricLocalStatement → DegreeStatement →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
      (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (rd Lval : ℝ),
      IsIntersectionSystem II → T.Conv II → T.Proportional → T.Prop6 II frob → 1 ≤ rd → (∀ p ∈ T.bad, p.Prime) →
      (∀ c τ, ∃ R : RootFlat (T.M 2 c) τ, NearRecord N T.bad rd Lval R.ht) → T.PropF II 4 rd Lval

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

