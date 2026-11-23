module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.HermitianLattices.StatementLat
public import Formalism.GradedWeylDivisibility.StatementA

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.StatementB
section
noncomputable section

open Matrix

namespace Formalism.UG

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

def gram (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) : Matrix n n K :=
  fun i j => h (Pi.single i 1) (Pi.single j 1)

def glEquiv (g : GL n K) : (n → K) ≃ₗ[K] (n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K) (Matrix.GeneralLinearGroup.toLin g)

def GlEquivApply : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (g : GL n K) (x : n → K),
    glEquiv g x = (g : Matrix n n K) *ᵥ x

def HformGram : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K),
    h x y = hform (starRingEnd K) (gram h) x y

def HermBridge : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (g : GL n K),
    g ∈ UJ (starRingEnd K) (gram h) ↔ glEquiv g ∈ Formalism.HermitianLatticesTheory.isom h

def HermBridgeSurj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K), ∀ u ∈ Formalism.HermitianLatticesTheory.isom h, ∃ g : GL n K, glEquiv g = u

end Formalism.UG
end
end

-- bundled from Formalism.SatakeDualWeyl.StatementW
section
noncomputable section

open MvPolynomial

namespace Formalism.UG

def dwAct (R : Type) [CommRing R] (r n : ℕ) (g : GL (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  Formalism.GradedWeylDivisibility.rowAct R (n := n) ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)

def DwActMul : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (g h : GL (Fin r) R),
    dwAct R r n (g * h) = (dwAct R r n g).comp (dwAct R r n h) ∧ dwAct R r n 1 = AlgHom.id R _

def DwStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν

def WeylGLStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν

def WeylGLStableLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν

end Formalism.UG
end
end

