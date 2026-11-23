module

public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEFinal

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)

structure BrData (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) where
  I : BaseId W
  C₁ : Coord W I T₁
  C₂ : Coord W I T₂
  C₀ : Coord W I W.one
  h : CoordHom C₁ C₂ F
  e₀ : C₀.V
  ϖ : O
  eO : ℕ
  u : Oˣ
  x : Oˣ
  Ks : ℕ → Type
  [ksRing : ∀ s, CommRing (Ks s)]
  [ksAlg : ∀ s, Algebra LL (Ks s)]
  Δ : Type

attribute [instance] BrData.ksRing BrData.ksAlg

variable {W}

structure BrProps {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} (D : BrData W T₁ T₂ F)
    (Cu : Formalism.ExponentWindows.E.Cuts n) (kd : ZMod n → Formalism.ExponentWindows.Kind) (bb : ZMod n → ℕ)
    (j g G₀ Sz η hh sig rr : ℕ) : Prop where

  irr : Irreducible D.ϖ

  prim : Formalism.ExponentWindows.E.PrimBase D.I.Bs D.ϖ D.eO

  u_eq : (D.u : O) = 1 + (D.I.Bs.ℓ : O) * (D.x : O)

  lat₁ : Formalism.ExponentWindows.E.FinalLat (latOf D.C₁) Cu kd bb j G₀ Sz η hh

  lat₂ : Formalism.ExponentWindows.E.FinalLat (latOf D.C₂) Cu kd bb j G₀ Sz η hh

  unit : Formalism.ExponentWindows.E.PrimUnit (latOf D.C₀) D.e₀

  rho : ∀ c ∈ Cu.cuts, ∀ w,
    (latOf D.C₁).Wc Cu (Formalism.ExponentWindows.E.LamOf D.I.Bs Cu (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb)) c w →
    ∀ y z, (latOf D.C₁).IsRho c j (Formalism.ExponentWindows.E.parM D.I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ Zf D.C₁

  ext : ∀ κ ∈ Zf D.C₂, ∃ Y : Formalism.ExponentWindows.E.Ext (latOf D.C₂) (latOf D.C₀), Y.Rep D.e₀ κ.1 κ.2 ∧
    Formalism.ExponentWindows.E.PrimExt Y D.e₀ Cu j G₀ rr (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb)

  wprime : Formalism.ExponentWindows.E.WPrimeCuts (latHomOf D.h) Cu rr

  arcs : ∀ c ∈ Cu.cuts, Formalism.ExponentWindows.E.FinalArc (latHomOf D.h) c (Cu.ell c)
    (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb c) LL D.Ks D.Δ D.ϖ D.u j (Formalism.ExponentWindows.E.parM D.I.Bs.ℓ hh g) g G₀ Sz η
    (Formalism.ExponentWindows.E.kindAt kd c) (Formalism.ExponentWindows.E.sizeAt bb c)

variable (W) [Fintype (K →ₐ[Qp] LL)]

def Realised : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (Mb₁ hb₁ Mb₂ hb₂ : ZMod n → ℕ) (hC : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      (∀ i, JumpsAtE PD T₁ W.emb i (Set.Icc (-(Mb₁ i : ℤ)) (hb₁ i))) →
      (∀ i, JumpsAtE PD T₂ W.emb i (Set.Icc (-(Mb₂ i : ℤ)) (hb₂ i))) →
      WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (Mb₁ + hb₁) (Mb₂ + hb₂) cuts arcLen) ty cuts
        arcLen →
      ∃ D : BrData W T₁ T₂ F, BrProps D (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
        (sigPar PD.p (gPar Gp S η) h j) (rrPar PD.p n (Mb₁ + hb₁) (Mb₂ + hb₂) cuts)

variable {W}

end Formalism.MainNotions.WachCoordinates.Br
