module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition

section Series
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
  {N : NumD C}

end Series

structure TowerIso {C : Type} [Field C] (N N' : NumD C) (n : ℕ) where

  io : ∀ j : ℕ, N.QT ((n ^ j) ^ 2) → N'.QT ((n ^ j) ^ 2)

  eqv : ∀ j p q, N'.QEq (io j p) (io j q) ↔ N.QEq p q

  onto : ∀ j p', ∃ p, N'.QEq (io j p) p'

  mul : ∀ j p q, N'.QEq (io j (p * q)) (io j p * io j q)

  incl : ∀ j (p : N.QT ((n ^ j) ^ 2)) (q : N.QT ((n ^ (j + 1)) ^ 2)) (q' : N'.QT ((n ^ (j + 1)) ^ 2)),
    q.1.1.toAdd = n ^ 2 • p.1.1.toAdd → q.1.2 = p.1.2 →
    q'.1.1.toAdd = n ^ 2 • (io j p).1.1.toAdd → q'.1.2 = (io j p).1.2 → N'.QEq (io (j + 1) q) q'

  wp : ∀ j p q, N'.wp (io j p) (io j q) = N.wp p q

def TowerIso.Proportional {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (w : TowerIso N N' n) (c₀ : C) : Prop :=
  ∀ j p, ∃ v, HasSum (N.txT (n ^ j) p) v ∧ HasSum (N'.txT (n ^ j) (w.io j p)) (c₀ * v)

section Rec
variable {V : Type} [CommRing V] [IsDomain V] {D D' : DegPre V} {C : Type} [Field C] [Algebra (FractionRing V) C]
  {N N' : NumD C}

def TowerIso.RationalAt {n : ℕ} (w : TowerIso N N' n) (ν : NumOf D C N) (ν' : NumOf D' C N') (j : ℕ) : Prop :=
  ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D C ((n ^ j) ^ 2)) (p' pσ' : QkPt D' C ((n ^ j) ^ 2))
    (q qσ : N.QT ((n ^ j) ^ 2)) (q' qσ' : N'.QT ((n ^ j) ^ 2)),
    QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → ν.QPt p q → ν.QPt pσ qσ → ν'.QPt p' q' → ν'.QPt pσ' qσ' →
    N'.QEq (w.io j q) q' → N'.QEq (w.io j qσ) qσ'

def Carries (e : IsPullDeg (RingHom.id V) D D') {k : ℕ} (p : QkPt D C k) (p' : QkPt D' C k) : Prop :=
  e.xe p'.y = p.y ∧ ∀ χ : D'.X, GenRel (F := C) e.w (p'.g.s χ) (p.g.s (e.xe χ)) 1

def TowerIso.InducedBy {n : ℕ} (w : TowerIso N N' n) (ν : NumOf D C N) (ν' : NumOf D' C N')
    (e : IsPullDeg (RingHom.id V) D D') : Prop :=
  ∀ j (q : N.QT ((n ^ j) ^ 2)), ∃ (p : QkPt D C ((n ^ j) ^ 2)) (p' : QkPt D' C ((n ^ j) ^ 2)) (q' : N'.QT ((n ^ j) ^ 2)),
    ν.QPt p q ∧ ν'.QPt p' q' ∧ Carries e p p' ∧ N'.QEq (w.io j q) q'
end Rec

def RecognitionSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
  ∀ (D D' : DegData V (IsLocalRing.maximalIdeal V)) (n : ℕ), n.Prime → Odd n → IsUnit (n : V) →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing V) C],
    CExt V (IsLocalRing.maximalIdeal V) C →
  ∀ (N N' : NumD C) (ν : NumOf D.toPre C N) (ν' : NumOf D'.toPre C N') (w : TowerIso N N' n) (c₀ : C),
    w.Proportional c₀ → (∃ j, 1 ≤ j ∧ w.RationalAt ν ν' j) →
    ∃ e : IsPullDeg (RingHom.id V) D.toPre D'.toPre, w.InducedBy ν ν' e


end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition
end
