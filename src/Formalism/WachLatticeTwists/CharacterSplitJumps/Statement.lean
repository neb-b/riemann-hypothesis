module

public import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def QuotShape {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type}
    [AddCommGroup X] [Module O X] (Hc F : Submodule O X) (deg : ℕ) : Prop :=
  ∃ (Cy : Type) (_ : AddCommGroup Cy) (_ : Module O Cy)
    (ι : (Fin deg → KO O) →ₗ[O] (Hc ⧸ F.comap Hc.subtype))
    (π : (Hc ⧸ F.comap Hc.subtype) →ₗ[O] Cy),
    Function.Injective ι ∧ Function.Exact ι π ∧ ∃ c0 : Cy, ∀ y : Cy, ∃ a : O, y = a • c0

section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

end Defs

def HZeroHypotheses {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (U : Finset ℤ) : Prop :=
  1 ≤ m ∧ (ℓ = 2 → 2 ≤ m) ∧ PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m ∧ 0 ∉ U ∧ U.Nonempty ∧
  D.piece.Inputs w U 0 ∧ D.Union ∧ D.Flat ∧ D.LES ∧ D.Inv

structure HZeroRowPlaceData (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (d : Type) (Mrow : Type) [AddCommGroup Mrow] [Module O Mrow] where

  D : InvariantsCohomologyData ℓ

  N : Submodule O (d → KO O)
  idn : D.M ≃+ N

  Cs : Type
  [gCs : AddCommGroup Cs]
  [mCs : Module O Cs]
  con : N →ₗ[O] Cs
  inc : Mrow →ₗ[O] Cs

attribute [instance] HZeroRowPlaceData.gCs HZeroRowPlaceData.mCs

def HZeroTorsionLengthOnePlace : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type) [Fintype d] (Mrow : Type) [AddCommGroup Mrow] [Module O Mrow]
    (B : HZeroRowPlaceData ℓ O d Mrow) (w : ℤ_[ℓ]ˣ) (m : ℕ) (U : Finset ℤ),
    HZeroHypotheses B.D w m U → Function.Injective B.inc →
    Submodule.torsion O B.Cs ≤ LinearMap.range B.con →
    ∃ H : Submodule O (d → KO O), (∀ x ∈ H, ((ℓ : O) ^ c0 ℓ m U) • x = 0) ∧
      Module.length O (Submodule.torsion O Mrow) ≤ Module.length O H

def StatBKbConv : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A HV HT' HV' : Type) [AddCommGroup A] [Module O A]
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT']
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV'),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : A, (∀ t, pr x t = 0) → x = 0) →
    (HfV.restrictScalars O).map q = annih pr ((HfV'.restrictScalars O).comap j')

def StatRowBK : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (X : Type) [AddCommGroup X] [Module O X] (Hc : Submodule O X)
    (HV Cs HV' : Type)
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup Cs] [Module O Cs] [Module.Finite O Cs]
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] Hc) (j' : Cs →ₗ[O] HV') (pr : Hc →ₗ[O] Cs →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV')
    (F : Submodule O X) (Fs : Submodule O Cs),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : Hc, (∀ t, pr x t = 0) → x = 0) →
    F = ((HfV.restrictScalars O).map q).map Hc.subtype → Fs = (HfV'.restrictScalars O).comap j' →
    F = (annih pr Fs).map Hc.subtype

end Formalism.RepresentationBoundsCohomology.JT
