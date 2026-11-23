module

public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

variable {D : D7}

structure AlgPkg (G : DV.Geo D.what₂.LL) (Tau : Type) [Fintype Tau] (N : ℕ) (Comp : Type) [Fintype Comp] where

  Yv : Comp → G.Var

  Ybd : ∀ c, G.Cl (Yv c)

  bd : ∀ c, G.Dv (Yv c)
  bd_supp : ∀ c, G.supp (Yv c) (bd c) = Ybd c

  Lw : ∀ c, (Tau → Fin N → ℤ) →+ G.Dv (Yv c)

  dim_eq : ∀ c, G.dim (Yv c) = Formalism.DegreeFormula.dimFl Tau N

  degA : ∀ c, G.Adl (Yv c) → ℝ

  degA_ofW : ∀ c (Δ : G.Dv (Yv c)) (W : HLat D.what₂.LL) (ι : W.V →ₗ[D.what₂.LL] G.Fn (Yv c)),
    degA c (G.ofW (Yv c) Δ W ι) = (G.inter (Yv c) (fun _ => Δ) : ℝ)

  degA_twist : ∀ c Lb ci cf, degA c (G.twist (Yv c) Lb ci cf) = degA c Lb

  semipos : (∀ c, G.Adl (Yv c)) → Prop
  nefFib : (∀ c, G.Adl (Yv c)) → Prop

  Mbar : ℝ → (Tau → Fin N → ℝ) → ℚ → ∀ c, G.Adl (Yv c)

namespace AlgPkg

variable {G : DV.Geo D.what₂.LL} {Tau : Type} [Fintype Tau] {N : ℕ} {Comp : Type} [Fintype Comp]
  (A : AlgPkg G Tau N Comp)

def ALB : Type := ∀ c, G.Adl (A.Yv c)

def arSelfC (L : A.ALB) (c : Comp) : ℝ := G.arTop (A.Yv c) (L c)

def geoC (L : A.ALB) (c : Comp) : ℝ := A.degA c (L c)

def arVol (L : A.ALB) : ℝ := ∑ c, G.arVol (A.Yv c) (L c)

def arNef (L : A.ALB) : Prop := ∀ c, G.nefA (A.Yv c) (L c)

end AlgPkg

end Formalism.L2.Geo
end
end

-- bundled from Formalism.LocalToGlobal.LatticeGeometry.NormDetInf
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

structure CxPkg (Tau : Type) [Fintype Tau] (N j : ℕ) (Comp : Type) [Fintype Comp] where

  Γ : Comp → Subgroup (Tau → GL (Fin j ⊕ Fin (N - j)) ℂ)
  Γ_le : ∀ c, Γ c ≤ Formalism.DegreeFormula.UpqI Tau j (N - j)

  volC : Comp → ℝ
  volC_pos : ∀ c, 0 < volC c

  rfn : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  rfn_ge : ∀ z, Real.exp 1 ≤ rfn z

  hLo : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  hUp : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  hLo_le : ∀ z, 0 < hLo z ∧ hLo z ≤ hUp z

  connN : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  curvN : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ

  normDetInf : Tau → (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ

namespace CxPkg

variable {Tau : Type} [Fintype Tau] {N j : ℕ} {Comp : Type} [Fintype Comp] (X : CxPkg Tau N j Comp)

def XC : Type := Σ c, XCc Tau j (N - j) (X.Γ c)

def compOf : X.XC → Comp := Sigma.fst

def vol : ℝ := ∑ c, X.volC c

def chern : MvPolynomial (DV.Rt Tau N) ℝ →ₗ[ℝ] ℝ := chernOf Tau N X.vol

end CxPkg

end Formalism.L2.Geo
end
end

