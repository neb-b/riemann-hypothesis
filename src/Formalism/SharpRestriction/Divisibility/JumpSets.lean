module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.JumpSetsAlt

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.UG TensorProduct Finset NumberField IsDedekindDomain

abbrev AmbT (R : Type) [CommRing R] (ι : Type) (N : ℕ) : Type :=
  PiTensorProduct R (fun _ : ι => MvPolynomial (Fin N × Fin N) R)

abbrev Cg (R : Type) [CommRing R] (ι : Type) (N : ℕ) : Type := (ι → GL (Fin N) R) × Rˣ

abbrev GE (D : D7) : Type := D.nd.Om ≃ₐ[D.host.E] D.nd.Om

abbrev Ob (l : ℕ) [Fact l.Prime] : ValuationSubring (Om l) :=
  (Valued.v (R := Om l) (Γ₀ := NNReal)).valuationSubring

abbrev kb (l : ℕ) [Fact l.Prime] : Type := IsLocalRing.ResidueField (Ob l)

abbrev ResRep (D : D7) (l : ℕ) [Fact l.Prime] : Type := GE D → Polynomial (kb l)

structure Prov (D : D7) where

  O : ℕ → Type
  [instO : ∀ l, CommRing (O l)]
  [domO : ∀ l, IsDomain (O l)]
  [dvrO : ∀ l, IsDiscreteValuationRing (O l)]
  [czO : ∀ l, CharZero (O l)]
  [algZ : ∀ (l : ℕ) [Fact l.Prime], Algebra ℤ_[l] (O l)]
  [topO : ∀ l, TopologicalSpace (O l)]

  l_mem : ∀ l, l.Prime → ((l : ℕ) : O l) ∈ IsLocalRing.maximalIdeal (O l)

  fin_l : ∀ l, l.Prime → Finite (O l ⧸ Ideal.span {((l : ℕ) : O l)})

  Gf : Type
  [instGf : Group Gf]
  Gam : Subgroup Gf

  gamE : Gam →* GL (Fin D.R.nV) D.host.E
  gamE_inj : Function.Injective gamE

  Lev : ℕ → Type

  hyp : ∀ l, Lev l → Prop
  Kl : ∀ l, Lev l → Subgroup Gf

  fin_class : ∀ l (c : Lev l), Finite (ClassSet Gam (Kl l c))

  fin_stab : ∀ l (c : Lev l) (g : Gf), (stabAt Gam (Kl l c) g).Finite

  kapK : ∀ l (c : Lev l), Kl l c →* (D.what₂.Tau → GL (Fin D.R.nV) (O l))

  typ : ∀ l (c : Lev l), Kl l c →* (O l)ˣ

  cf : ∀ l (_lam : D.what₂.Tau → DomWeight D.R.nV),
    Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) (AmbT (O l) D.what₂.Tau D.R.nV)

  cf_def : ∀ l (lam : D.what₂.Tau → DomWeight D.R.nV) (γ : Cg (O l) D.what₂.Tau D.R.nV)
    (x : D.what₂.Tau → MvPolynomial (Fin D.R.nV × Fin D.R.nV) (O l)),
    cf l lam γ (PiTensorProduct.tprod (O l) x) =
      ((γ.2 : (O l)ˣ) : O l) •
        PiTensorProduct.tprod (O l) (fun τ => roundAct (O l) D.R.nV (lam τ) (γ.1 τ) (x τ))

  Hk : ∀ l, Lev l → Type
  [instHk : ∀ l c, CommRing (Hk l c)]
  [algHk : ∀ l c, Algebra (O l) (Hk l c)]
  [modHk : ∀ l c (A : Type) [AddCommGroup A] [Module (O l) A]
    (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A),
    Module (Hk l c) (AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c))))]
  [towHk : ∀ l c (A : Type) [AddCommGroup A] [Module (O l) A]
    (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A),
    IsScalarTower (O l) (Hk l c)
      (AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c))))]

  hk_transl : ∀ l (c : Lev l) (T : Hk l c), ∃ el : Gf →₀ O l,
    ∀ (A : Type) [AddCommGroup A] [Module (O l) A]
      (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A)
      (f : AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c)))) (g : Gf),
      ((T • f : AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c)))) : Gf → A) g =
        el.sum fun x a => a • (f : Gf → A) (g * x)

  bw : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    LocBridge l D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (O l)

  iota : ∀ (l : ℕ) [Fact l.Prime], D.host.E →+* Om l

  ep : ℕ → Bool

  attached : ∀ (l : ℕ) [Fact l.Prime] (_h : ℕ) (c : Lev l), Ideal (Hk l c) → ResRep D l → Prop

attribute [instance] Prov.instO Prov.domO Prov.dvrO Prov.czO Prov.algZ Prov.topO Prov.instGf Prov.instHk Prov.algHk
  Prov.modHk Prov.towHk

variable {D : D7}

def excSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d, D.host.pde, D.host.pde'}

def ramSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d}

end Formalism.MainNotions.JumpSetsAlt

end
