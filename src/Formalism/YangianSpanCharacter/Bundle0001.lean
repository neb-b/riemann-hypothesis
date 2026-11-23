module

public import Formalism.YangianSpanCharacter.StatementT

@[expose] public section

-- bundled from Formalism.YangianSpanCharacter.ExchangeGen
section
namespace Formalism.YangianSpanCharacter.T

open Matrix

def E1 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def E2 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

end Formalism.YangianSpanCharacter.T
end

-- bundled from Formalism.YangianSpanCharacter.StatementY
section
namespace Formalism.YangianSpanCharacter.Y

open Matrix Formalism.YangianSpanCharacter.T

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

def lf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 1 0

def mf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 0 1

def hf (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (u : 𝕜) : A := q u • (τinv u * τinv (u + 1))

def eta (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (lf t τinv u - lf t τinv v)

def mu (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (mf t τinv u - mf t τinv v)

def ModHyp (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜) : Prop :=
  (∀ (u v : 𝕜) (i j k l : Fin 2),
      (u - v) • (t u i j * t v k l - t v k l * t u i j) = t u k j * t v i l - t v k j * t u i l) ∧
    (∀ Y : 𝕜, (t (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J A * t Y = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ u ∈ S, t u 1 1 * τinv u = 1 ∧ τinv u * t u 1 1 = 1) ∧
    (∀ u v : 𝕜, Commute (t u 1 1) (t v 1 1)) ∧
    (∀ u v : 𝕜, Commute (t u 1 0) (t v 1 0))

def Y1 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v)

def Y1' : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v

def Y3 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → u + 1 ∈ S → u - 1 ∈ S → v ∈ S → v + 1 ∈ S → u ≠ v →
      (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
        hf τinv q v - hf τinv q (u - 1)

end Formalism.YangianSpanCharacter.Y
end

