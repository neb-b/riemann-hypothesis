module

public import Mathlib

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

structure Letters (ι : Type*) where
  vec : ι → Bool

def genMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun a b => X (a, b)

abbrev GLCoord (R : Type*) [CommRing R] (n : ℕ) := Localization.Away (genMat R n).det

def lastIdx (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩


open Classical in
def glAct (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R := by
  classical
  exact ∑ l : ι,
    if l ∈ S then
      (if LL.vec l then (LinearMap.mulLeft R (X (l, a))) ∘ₗ (pderiv (l, b)).toLinearMap
       else -((LinearMap.mulLeft R (X (l, b))) ∘ₗ (pderiv (l, a)).toLinearMap))
    else 0

abbrev GLOps (n : ℕ) (K V : Type*) [Field K] [AddCommGroup V] [Module K V] := Fin n → Fin n → Module.End K V

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def weightSp (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨅ a, LinearMap.ker (E a a - (mu a : K) • (1 : Module.End K V))

def Dominant (mu : Fin n → ℤ) : Prop := Antitone mu

def divPowE (E : GLOps n K V) (a b : Fin n) (k : ℕ) : Module.End K V := ((k.factorial : K)⁻¹) • (E a b) ^ k

def binomE (E : GLOps n K V) (a : Fin n) (k : ℕ) : Module.End K V :=
  ((k.factorial : K)⁻¹) • ((List.range k).map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod

def UZgens (E : GLOps n K V) : Set (Module.End K V) :=
  {u | (∃ a b k, a ≠ b ∧ u = divPowE E a b k) ∨ (∃ a k, u = binomE E a k)}

def UZmon (E : GLOps n K V) : Submonoid (Module.End K V) := Submonoid.closure (UZgens E)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def otherWts (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V := ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu

def Nabla [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Set V :=
  {x | ∀ u ∈ UZmon E, ∃ c : O, u x - (algebraMap O K c) • v ∈ otherWts E lam}

def glOps (K : Type*) [Field K] {ι : Type*} [Fintype ι] (n : ℕ) (LL : Letters ι) (S : Set ι) :
    GLOps n K (MvPolynomial (ι × Fin n) K) :=
  fun a b => glAct K LL S a b

def colH {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ mu m).card

end Formalism.InvariantFactorPaths.ColumnFamilies
