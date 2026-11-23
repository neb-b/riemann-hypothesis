module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCx GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo (Integ IsFnL)
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

instance algAt (S : Setup A n p) (w : Plc E) : Algebra S.G.F (w.adicCompletion E) := inferInstanceAs (Algebra E (w.adicCompletion E))

def Spl (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ) : Type := {w : Plc E // IsSplitAt w ∧ (p : 𝓞 E) ∉ w.asIdeal}

abbrev fac {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Spl E p) : Loc S.G.GAf (GL (Fin n) (w.1.adicCompletion E)) :=
  T.at hc w.1 w.2.1 w.2.2

structure Half (q : ℕ) (W : Finset (Spl E p)) : Prop where
  above : ∀ w ∈ W, (q : 𝓞 E) ∈ w.1.asIdeal
  all : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → ∃ w ∈ W, w.1 = u ∨ cj w.1 = u
  apart : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → GlobalTheory.Cong.Apart w.1 w'.1

def AdmCusp : Prop :=
  ∀ (X : Type) [Group X] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (Ty : TyLev X (GL (Fin n) k)),
    IsOpen (Ty.J : Set (GL (Fin n) k)) → IsCompact (Ty.J : Set (GL (Fin n) k)) → IsOpen (Ty.ψ.ker : Set Ty.J) →
    (∀ (σ : SmIrr (GL (Fin n) k)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ f, Ty.admitted f → ∀ h : X, Ty.L.pr h = 1 → NoConst fun g => f (Ty.L.loc g * h)

end UpperTheory.Gal.Spc
