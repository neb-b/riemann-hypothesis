module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {c c' : Coeff l}

def incl (h : c.F ≤ c'.F) : c.F →+* c'.F := (IntermediateField.inclusion h).toRingHom

def Res (_h : c.F ≤ c'.F) (S : Type) : Type := S

instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] : CommRing (Res h S) := inferInstanceAs (CommRing S)

instance (h : c.F ≤ c'.F) (S : Type) [CommRing S] [Algebra c'.F S] : Algebra c.F (Res h S) :=
  ((algebraMap c'.F S).comp (incl h)).toAlgebra

def unRes {h : c.F ≤ c'.F} {S : Type} [CommRing S] : Res h S ≃+* S := RingEquiv.refl S

variable {Xo : Moduli Dw l}

def ptDown (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FrPt Xo c (Res h S) where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen

def ptUp (h : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c (Res h S)) :
    FrPt Xo c' S where
  x := y.x
  x_over := y.x_over
  u := y.u
  tan := y.tan
  eig := y.eig
  basis := y.basis
  s := y.s
  gen := y.gen

def embRes (h : c.F ≤ c'.F) (σ' : c'.F →+* ℂ) : c.F →+* ℂ := σ'.comp (incl h)

variable {r : ℕ}

def unfUp (h : c.F ≤ c'.F) (σ' : c'.F →+* ℂ) (U : Unf Xo c (embRes h σ') r) : Unf Xo c' σ' r where
  Comp := U.Comp
  fin := U.fin
  X := U.X
  un k x := ptUp h (S := CAt σ') (U.un k x)

def unfFamUp (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : ∀ σ' : c'.F →+* ℂ, Unf Xo c' σ' r :=
  fun σ' => unfUp h σ' (U (embRes h σ'))

def ruleUp (h : c.F ≤ c'.F) : Rul Xo c →ₛₗ[incl h] Rul Xo c' where
  toFun f := fun p y => unRes (evR Xo c f (ptDown h y))
  map_add' f g := by
    funext p y
    exact evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (ptDown h y)
  map_smul' a f := by
    funext p y
    have e := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f (ptDown h y)
    show _ = incl h a • (unRes (evR Xo c f (ptDown h y)) : p.R)
    exact e.trans (Algebra.smul_def (incl h a) (unRes (evR Xo c f (ptDown h y)) : p.R)).symm

def IsComb (h : c.F ≤ c'.F) {m : ℕ} (b : Fin m → c'.F) (f : Fin m → Rul Xo c) (f' : Rul Xo c') : Prop :=
  ∀ (p : TRing c'.F) (y : FrPt Xo c' p.R),
    f' p y = ∑ i, algebraMap c'.F p.R (b i) * unRes (evR Xo c (f i) (ptDown h y))


variable (Xo)

def ActionExtends (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {G : Type} [Group G] (ρ : G →* Module.End c.F (cusp Xo c U a n))
    (ρ' : G →* Module.End c'.F (cusp Xo c' (unfFamUp h U) a n)) : Prop :=
  ∀ (g : G) (m : ℕ) (b : Fin m → c'.F) (f : Fin m → cusp Xo c U a n) (f' : cusp Xo c' (unfFamUp h U) a n),
    IsComb h b (fun i => (f i : Rul Xo c)) (f' : Rul Xo c') →
      IsComb h b (fun i => (ρ g (f i) : Rul Xo c)) (ρ' g f' : Rul Xo c')

end GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
