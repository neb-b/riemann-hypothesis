module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
section
noncomputable section

namespace Formalism.MainNotions.placeRankTwoOne

open Formalism.BasicNotions NumberField IsDedekindDomain

def NN (D : D7) : ℝ := (D.R.N D.R.m : ℝ)

def degLine (D : D7) (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ) : ℝ :=
  (∑ᶠ w, ρ w * lw D.what₂.LL (D.plEq w)) - (∑ σ, Real.log (r σ)) / (Module.finrank ℚ D.what₂.LL : ℝ)

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def idOf (D : D7) (τ : D.what₂.Tau)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.what₂.LL) D.what₂.LL :=
  Submodule.span (𝓞 D.what₂.LL) ((embTau D τ) '' {x | x ∈ I})

def ddEK (D : D7) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

def idMul {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (I : Submodule (𝓞 K) K) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {y | ∃ a ∈ I, ∃ z ∈ M, y = a • z}


open Classical in
def detW (D : D7) (τ : D.what₂.Tau) : D.what₂.Tau → Fin D.R.r → ℤ :=
  fun τ' _ => if τ' = τ then -1 else 0

def IsNV {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) (τ : D.what₂.Tau)
    (s : X.geo.Fn (X.Yv j c)) : Prop :=
  s ≠ 0 ∧ s ∈ X.geo.H0 (X.Yv j c) (X.Lw j c (detW D τ)) ∧
    s⁻¹ ∈ X.geo.H0 (X.Yv j c) (-(X.Lw j c (detW D τ)))

structure Loc (D : D7) (X : DivX D) where

  lieCK : HLat D.what₂.LL
  lieCK_good : lieCK.Good
  lieCK_rank : lieCK.rank = 1

  ell : D.what₂.Tau → HLat D.what₂.LL
  ell_good : ∀ τ, (ell τ).Good
  ell_rank : ∀ τ, (ell τ).rank = 1

  ellIso : ∀ τ, lieCK.V ≃ₗ[D.what₂.LL] (ell τ).V
  ellIso_lat : ∀ τ, (ell τ).L = (idMul (idOf D τ (D.host.AA0 * ddEK D)) lieCK.L).map
      ((ellIso τ).toLinearMap.restrictScalars (𝓞 D.what₂.LL))
  ellIso_norm : ∀ τ v (z : lieCK.V),
    Formalism.HermitianLatticesTheory.normAt (ell τ).b (ell τ).X v (ellIso τ z) = Formalism.HermitianLatticesTheory.normAt lieCK.b lieCK.X v z

  ell_Om : ∀ τ, D.gx.logOmMean τ = (ell τ).mu

  eH : ∀ τ, Submodule (𝓞 D.what₂.LL) (ell τ).V

  eH_eq : ∀ τ, eH τ = (idMul (idOf D τ D.host.AA0) lieCK.L).map
      ((ellIso τ).toLinearMap.restrictScalars (𝓞 D.what₂.LL))

  Comp_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → Nonempty (X.Comp j)

  PtF : ∀ j, X.Comp j → D.what₂.places.Pl → Type
  PtF_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c w, Nonempty (PtF j c w)
  pts_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c σ, Nonempty (X.geo.pts (X.Yv j c) σ)

  vHT : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  vSub : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  vLie : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  metH : ∀ j c τ σ, X.geo.Met (X.Yv j c) σ (X.Lw j c (detW D τ))

  vF : ∀ j c, D.what₂.Tau → ∀ w, X.geo.Fn (X.Yv j c) → PtF j c w → ℝ

  vF_smul : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ w (a : D.what₂.LL) (f : X.geo.Fn (X.Yv j c)) y, a ≠ 0 → IsNV X j c τ f →
    vF j c τ w (a • f) y = (vAdd (D.plEq w) a : ℝ) + vF j c τ w f y

  degHH_def : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ (s : X.geo.Fn (X.Yv j c)), IsNV X j c τ s →
    ∀ (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ), (∀ σ, 0 < r σ) →
      (∀ σ y, X.geo.pn (X.Yv j c) σ _ (metH j c τ σ) (X.geo.cx (X.Yv j c) σ s) y = r σ ^ 2) →
      (∀ w y, vF j c τ w s y = ρ w) → (Function.support ρ).Finite →
      X.degHH j c τ = degLine D r ρ

  thSup : ∀ u i, (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → ℝ

variable (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : Loc D X)

def LL0 : ℝ :=
  Real.log (large₂.sc.b * D.host.rdE) * Real.log (Real.log large₂.sc.x) + |large₂.logDerivativeAtOne| + Real.log large₂.sc.x

def dimY : ℕ := D.R.f * (D.R.r.choose 2)

abbrev LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : LocF Fm)

end Fam

end Formalism.MainNotions.placeRankTwoOne

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.PrinLevClass
section
noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

structure PrinLev {D : D7} (V : DivX D) where

  κg : V.Lev

  κs : V.Lev
  κg_pr : V.levPr κg = {D.host.g 0, D.host.g 1}
  κs_pr : V.levPr κs = {D.host.g 0, D.host.g 1, 3, 5}

def LevB {D : D7} {V : DivX D} (P : PrinLev V) (κ : V.Lev) : Prop := κ = P.κg ∨ κ = P.κs

abbrev PrinLevF {eps : ℝ} (Fm : FamP eps) : Type :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), PrinLev (Fm.X x i)

end Formalism.MainNotions.DIV.Align

end
end

