module

public import Mathlib

@[expose] public section

noncomputable section

open PowerSeries

namespace GlobalTheory.NB

structure Fr (l : ℕ) (O : Type) [CommRing O] where
  prime : l.Prime
  odd : l ≠ 2
  l_nonunit : ¬ IsUnit (l : O)

  root : ∃ x : O, Associated (x ^ (l - 1)) (l : O)
  e : ℕ
  s : ℕ
  es : e * s = l - 1
  ϖ : Fin e → O
  ϖ_val : ∀ τ, Associated (ϖ τ ^ e) (l : O)
  ϖ_sub : ∀ τ τ', τ ≠ τ' → Associated (ϖ τ - ϖ τ') (ϖ τ)
  E : O⟦X⟧
  E_def : E = ∏ τ, (X - C (ϖ τ))
  φ : O⟦X⟧ →ₐ[O] O⟦X⟧
  γ : O⟦X⟧ →ₐ[O] O⟦X⟧
  comm : ∀ a, φ (γ a) = γ (φ a)
  u : (O⟦X⟧)ˣ
  φ_X : φ X = (u : O⟦X⟧) * X * E ^ s
  κ : (O⟦X⟧)ˣ
  γ_X : γ X = X * (1 + (κ : O⟦X⟧) * E)
  χ : Oˣ
  χ_gen : Associated ((χ : O) - 1) (l : O)
  χ_zero : constantCoeff (1 + (κ : O⟦X⟧) * E) = (χ : O) ^ s

  lev : Fin e → (O⟦X⟧ ≃ₐ[O] O⟦X⟧)
  lev_X : ∀ τ, lev τ X = X + C (ϖ τ)

  χ_lev : ∀ τ, ∃ w : O⟦X⟧, γ (X - C (ϖ τ)) = (X - C (ϖ τ)) * w ∧ constantCoeff (lev τ w) = (χ : O)

  lvl_red : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ a ^ 2 → (φ ^ k) E ∣ a

  lvl_triv : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ (γ ^ (l ^ k)) a - a

  lvl_inv : e = 1 → ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ γ a - a → ∃ c : O, (φ ^ k) E ∣ a - C c

  EE : Type
  [eeRing : CommRing EE]
  [eeAlgA : Algebra O⟦X⟧ EE]
  [eeAlgO : Algebra O EE]
  [eeTow : IsScalarTower O O⟦X⟧ EE]
  EE_inj : Function.Injective (algebraMap O⟦X⟧ EE)
  EE_X : IsUnit (algebraMap O⟦X⟧ EE X)
  EE_complete : IsAdicComplete (Ideal.span {(l : EE)}) EE
  EE_dense : ∀ (x : EE) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ),
    (l : EE) ^ k ∣ x * algebraMap O⟦X⟧ EE (X ^ m) - algebraMap O⟦X⟧ EE a
  EE_sat : ∀ (a : O⟦X⟧) (k : ℕ), (l : EE) ^ k ∣ algebraMap O⟦X⟧ EE a → (l : O⟦X⟧) ^ k ∣ a
  φE : EE →ₐ[O] EE
  φE_ext : ∀ a, φE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (φ a)
  γE : EE →ₐ[O] EE
  γE_ext : ∀ a, γE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (γ a)

  coeffRing : ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O),
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ CharZero O := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow

open Classical

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

abbrev ι : O⟦X⟧ →+* R.EE := algebraMap O⟦X⟧ R.EE

def N0 (r : ℕ) : Submodule O⟦X⟧ (Fin r → R.EE) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap O⟦X⟧ R.EE)

variable [IsDomain O]

end Fr

structure Sys {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) where
  M : ℕ
  Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G_one : ∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, G i = 1 + (X : O⟦X⟧) • B
  Φ_inv : ∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧), Φ i * Ψ = R.E ^ k • (1 : Matrix _ _ _)
  comm : ∀ i, R.E ^ M • (G i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (G (i - 1)).map R.φ)

abbrev DD {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) : Type := ZMod n → Fin r → R.EE

namespace Sys

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)

def φl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  ((Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι).mulVecLin.restrictScalars O).comp
    (R.φE.toLinearMap.compLeft (Fin r))

def γl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  (((S.G i).map R.ι).mulVecLin.restrictScalars O).comp (R.γE.toLinearMap.compLeft (Fin r))

def φD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.φl i).comp (LinearMap.proj (i - 1))

def γD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.γl i).comp (LinearMap.proj i)

def Z1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.ker ((S.γD - LinearMap.id).coprod (-(S.φD - LinearMap.id)))

def B1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.range ((S.φD - LinearMap.id).prod (S.γD - LinearMap.id))

variable [IsDomain O]

end Sys

structure Hom {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} (S : Sys R n r)
    (S' : Sys R n r') where
  F : ZMod n → Matrix (Fin r') (Fin r) O⟦X⟧
  φ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.φl i x) = S'.φl i (((F (i - 1)).map R.ι).mulVec x)
  γ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.γl i x) = S'.γl i (((F i).map R.ι).mulVec x)

namespace Hom

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' r'' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  {S'' : Sys R n r''} (F : Hom S S')

def comp (F' : Hom S' S'') (F : Hom S S') : Hom S S'' where
  F := fun i => F'.F i * F.F i
  φ_comm := fun i x => by
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.φ_comm,
      F'.φ_comm]
  γ_comm := fun i x => by
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.γ_comm, F'.γ_comm]

end Hom

end GlobalTheory.NB
