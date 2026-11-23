module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)

def latIota : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

variable {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F)

abbrev sigB : T.Q.c.F →+* ℂ := c'.F.val.toRingHom.comp (incF T.Q.c c' hle)

abbrev Cmp : Type := (T.U ((i : ℕ) + 1) (sigB T hle)).Comp

variable (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i)

variable (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n₀ : ℕ) (v₀ : (R.MW i (sg0 D A)).Vec)
  (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))

variable (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
  (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
  (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank)
  {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
  (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F)

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters
