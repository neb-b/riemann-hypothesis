module

public import Mathlib

@[expose] public section

namespace Formalism.YangianSpanCharacter.T

open Matrix

def J (A : Type*) [Ring A] : Matrix (Fin 2) (Fin 2) A := !![0, 1; -1, 0]

def Tm {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap R A Y + p, -c; ci, 0]

def WeylRel {A : Type*} [Ring A] (p c ci : A) : Prop :=
  c * ci = 1 ∧ ci * c = 1 ∧ p * c = c * p + c

def T1 {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then Tm Y p c ci ik.1 jl.1 else 0

def T2 {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (Y : R) (p c ci : A) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then Tm Y p c ci ik.2 jl.2 else 0

def Pf (A : Type*) [Ring A] : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.2 ∧ ik.2 = jl.1 then 1 else 0

def Um {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (s : R) : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; -algebraMap R A s, 1]

def Uinv {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (s : R) : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; algebraMap R A s, 1]

def TJT : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci : A) (Y : R),
    WeylRel p c ci → (Tm (Y + 1) p c ci)ᵀ * J A * Tm Y p c ci = J A

def RTT : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci : A) (Y Y' : R),
    WeylRel p c ci →
      ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * T1 Y' p c ci *
          T2 Y p c ci =
        T2 Y p c ci * T1 Y' p c ci *
          ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)

def PlaneWave : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci f : A) (s Y : R),
    f * c = c * f → f * ci = ci * f → p * f = f * p + algebraMap R A s * f * c →
      Um (A := A) s * Uinv s = 1 ∧ Uinv (A := A) s * Um s = 1 ∧
        Tm Y p c ci * Matrix.diagonal (fun _ => f) * Uinv s =
          Matrix.diagonal (fun _ => f) * Tm Y p c ci

def pt1 {R : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.of fun ik jl => M (ik.1, jl.2) (jl.1, ik.2)


end Formalism.YangianSpanCharacter.T
