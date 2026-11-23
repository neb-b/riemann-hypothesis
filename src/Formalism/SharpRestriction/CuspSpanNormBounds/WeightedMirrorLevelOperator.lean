module

public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Dr {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := ∏ a : Fin r, cOf x a

def GG {r : ℕ} (T T' : ℝ) (x : Fin (r + 1) → ℂ) : ℂ := ((Complex.normSq (zOf x) - T * T' : ℝ) : ℂ)

def mulF {m : ℕ} (f : (Fin m → ℂ) → ℂ) : Op m E := fun φ x => f x • φ x

def mulE {m : ℕ} (e : (Fin m → ℂ) → E →L[ℂ] E) : Op m E := fun φ x => e x (φ x)

def one {m : ℕ} : Op m E := fun φ => φ

def vecT {m : ℕ} (M : Matrix (Fin 2) (Fin 2) (Op m E)) (v : Fin 2 → Op m E) : Fin 2 → Op m E :=
  fun a => ∑ b : Fin 2, M a b ∘ v b

def vv {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y) (vv Y i (by omega))

def vvV {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y) (vvV Y i (by omega))

def Ar (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 0

def Br (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 1

def ArV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 0

def BrV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 1

def Ahat (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF Dr ∘ Ar r Y

def AhatV (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF (fun x => star (Dr x)) ∘ ArV r Y

def Rhat (r : ℕ) (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x)) ∘ (Q Y 1 0 ∘ Ar r Y + Q Y 1 1 ∘ Br r Y)

def dZ (r : ℕ) : Op (r + 1) E := wirt (Fin.last r)

def dZb (r : ℕ) : Op (r + 1) E := wirtBar (Fin.last r)

def nabla (r : ℕ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E := dZ r + mulE h

def l0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  -nabla r h - mulF (fun x => (Y + 1 / 2) * star (zOf x) / GG T T' x)

def m0 (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  dZb r - mulE hs - mulF (fun x => (Y - 1 / 2) * zOf x / GG T T' x)

section Lines

variable {k0 : ℕ} {Rho : Type*}

def xFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, xPoly (ρp ρ) Y • P ρ x

def xInvFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (xPoly (ρp ρ) Y)⁻¹ • P ρ x

def shInv {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (l : Fin k0)
    (Y : ℂ) : (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (Y + (ρp ρ l : ℂ))⁻¹ • P ρ x

end Lines

def SSnat {r : ℕ} (s : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) / Dr x) ∘ mulE s

def R0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) * GG T T' x) ∘ (l0 r T T' h Y ∘ Ar r Y + Br r Y)

def weightedMirrorLevelOperator (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => Dr x * GG T T' x) ∘ (m0 r T T' hs Y ∘ ArV r Y + BrV r Y)

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

structure Base (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where

  k0 : ℕ
  T : ℝ
  T' : ℝ
  u : Fin (k0 + 1) → ℝ
  u' : Fin (k0 + 1) → ℝ
  I : Set ℝ

  sgn : ℂ

  hs : E → E → ℂ

  fadj : (E →L[ℂ] E) → (E →L[ℂ] E)

  Rho : Type

  IsType : Rho → Prop

  rhoP : Rho → Fin k0 → ℝ

structure Ctx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ) where

  Dom : Set (Fin (r + 1) → ℂ)

  cls : Set ((Fin (r + 1) → ℂ) → E)

  clsF : Set ((Fin (r + 1) → ℂ) → E)

  beta : ((Fin (r + 1) → ℂ) → E) → ((Fin (r + 1) → ℂ) → E) → ℂ

  P : B.Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E

  Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)

  AA : Set (Op (r + 1) E)

  RR : (w : List (Bool × ℝ)) → Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E)

  TT : (w : List (Bool × ℝ)) → ℂ →
    Matrix (Fin 2) (Fin 2) (Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E))

  qw : List (Bool × ℝ) → ℂ → ℂ

  uw : (w : List (Bool × ℝ)) → (Fin w.length → Fin 2) → Op (r + 1) E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

def IsPlus (w : List (Bool × ℝ)) : Prop := ∀ a ∈ w, a.1 = true

end Ctx

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev GOp (n : ℕ) (E : Type*) := (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E

structure GCtx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) where

  nV : ℕ

  Eop : Fin nV → Fin nV → GOp nV E

  H : Matrix (Fin nV) (Fin nV) ℂ

  eIdx : Fin r → Fin nV

  Rad : GOp nV E → Op (r + 1) E → Prop

  PolyInv : Set (GOp nV E)

namespace GCtx

variable {r : ℕ} (Γ : GCtx E r)

def cminor (n : ℕ) (hn : n ≤ r) (u : ℂ) : GOp Γ.nV E := fun f g =>
  ∑ b : Fin n → Fin Γ.nV, if StrictMono b then
    (Matrix.det (Matrix.of fun (a j : Fin n) =>
      herm Γ.H (g.mulVec (Pi.single (b j) 1)) (Pi.single (Γ.eIdx ⟨a, by omega⟩) 1))) •
      qminorOp Γ.Eop (fun a : Fin n => Γ.eIdx ⟨a, by omega⟩) b u f g
  else 0

end GCtx

def DnVn {r : ℕ} (n : ℕ) (hn : n ≤ r) (Y : ℂ) (i : Fin 2) : Op (r + 1) E :=
  mulF (fun x => ∏ a : Fin n, cOf x ⟨a, by omega⟩) ∘ vv Y n hn i

def NoPoleRho (B : Base E) (Y : ℂ) : Prop := ∀ ρ : B.Rho, B.IsType ρ → ∀ l : Fin B.k0, Y + (B.rhoP ρ l : ℂ) ≠ 0

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

end Ctx

namespace Ctx

section Shape

variable {B : Base E} {r : ℕ} {C : Ctx B r} {SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E} {b : Bool}

end Shape

end Ctx

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

def bordDet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun (a b : Fin (r + 1)) =>
    herm (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) (if a = Fin.last r then w else fvec k r z a))

def omG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  prW k (wbPart k r z) (fun j => Hb k j j * bordDet k r z z' g (bvec (wI k r j)))

def omG' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  omG k r z' z (Hpk k r * g.conjTranspose * Hpk k r)

def evG {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) : ℂ :=
  MvPolynomial.eval (Sum.elim (fun ij => g ij.1 ij.2) (fun ij => star (g ij.1 ij.2))) p

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants
open Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.S.LevR
