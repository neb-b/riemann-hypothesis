module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial Filter Topology

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

def UU (x w : B.A) : ℕ := Nat.card {L : B.X x // w ∈ (L : Submodule K.O B.A)}

def Lin : Set (Submodule K.O B.A) :=
  {M | IsLat K.O K.E M ∧ (∀ y ∈ M, B.g * y ∈ M) ∧ ∀ y ∈ M, B.σ y ∈ M}

def sgnLat (M : Submodule K.O B.A) : ℚ :=
  let m : Fin (Module.finrank K.E B.A) → B.A :=
    Classical.epsilon fun m => Submodule.span K.O (Set.range m) = M
  K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
    Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det

def GG (u : B.A) : ℚ :=
  ∑ᶠ M ∈ {M ∈ B.Lin | u ∈ M ∧ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range}, B.sgnLat M

def rho (w : B.A) : ℕ :=
  Nat.card {k : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
    IsIntegral K.O ((((Quotient.out k : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A)}

def LieReg : Prop := B.σ B.g = B.g ∧ B.P.Separable

def Plus (x : B.A) : Prop := IsUnit x ∧ B.σ x = x

def LinLim (a : K.O) (x : B.A) (ℓ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (B.GG (x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
    atTop (𝓝 ℓ)

end InvAlg

def UQ.Small (K : UQ) (a : K.O) : Prop :=
  a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal K.O ∧ K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a

def CountIdentity : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ x w : B.A, B.Plus x → IsUnit w →
    B.GG (x * (w * B.σ w)) = (B.UU x w : ℚ)

def UnitaryLimit : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ x : B.A, B.Plus x →
    Tendsto (fun k : ℕ => (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
      atTop (𝓝 (B.N x : ℝ))

def LinearDescent : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable →
    ∀ a : K.O, K.Small a → ∀ (ℓ : (B₁.prod B₂).A → ℝ) (ℓ₁ : B₁.A → ℝ) (ℓ₂ : B₂.A → ℝ),
    (∀ x, (B₁.prod B₂).Plus x → (B₁.prod B₂).LinLim a x (ℓ x)) →
    (∀ x, B₁.Plus x → B₁.LinLim a x (ℓ₁ x)) → (∀ x, B₂.Plus x → B₂.LinLim a x (ℓ₂ x)) →
    ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      (-(K.q : ℝ)) ^ (val K.O (resultant B₁.P B₂.P)) *
        ((∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep) * ∑ᶠ k : B₂.Cl, ℓ₂ k.rep)

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatMapTmul
section
noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

end Det

def lagIdem {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (M : E) (a : ι → R) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    Polynomial.aeval M (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

end GlobalTheory.Pat
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj
section
open Matrix

noncomputable section

namespace GlobalTheory.Tw.Model

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

omit [StarRing R] in
theorem Phi_apply' (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega

omit [StarRing R] in
theorem Phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp

omit [StarRing R] in
theorem transpose_mul_Phi : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose

theorem Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp

omit [StarRing R] in
theorem Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [if_pos h, if_pos (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [theta, Phi_mul_transpose]

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]

theorem theta_mul_theta_inv {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    theta g * theta g⁻¹ = 1 := by
  rw [← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), theta_one]

theorem theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by
  rw [Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  rw [theta, theta_inv_eq hg]
  have h2 : ((Phi n R)ᵀ)ᴴ = Phi n R := by rw [← Phi_conjTranspose, conjTranspose_conjTranspose]
  simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, h2, Phi_conjTranspose]
  have hs : ((-1 : R) ^ (n - 1)) * ((-1 : R) ^ (n - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hP : Phi n R = ((-1 : R) ^ (n - 1)) • (Phi n R)ᵀ := by
    rw [Phi_transpose, smul_smul, hs, one_smul]
  have h3 : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    conv_lhs => rw [hP]
    nth_rewrite 2 [Phi_transpose]
    rw [smul_smul, hs, one_smul, Matrix.smul_mul, transpose_mul_Phi]
  have h4 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.transpose_mul, h3]; simp
  calc Phi n R * (Phi n R * (g * (Phi n R)ᵀ)) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h3, h4]; simp [smul_smul, hs]

theorem adj_eq {δ g : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (hg : IsUnit g) :
    adj δ g = (δ * theta g * δ⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Tw.Model
end
end

