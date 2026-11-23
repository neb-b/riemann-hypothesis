module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

def CsrOf : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R] (c : R ≃ₐ[k] R), c ^ 2 = 1 → ∀ n : ℕ,
    (∀ (J : Matrix (Fin n) (Fin n) R) (γ : GL (Fin n) R), IsUnit J.det → cong c γ J = J → IsCsr c n (cp γ)) ∧
    ∀ d : GL (Fin n) R, IsCsr c n (cp (d * th c d))

def ModelEx : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R), IsGal c 2 → ∀ (n : ℕ) (P : R[X]), IsCsr c n P → P.Separable →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (b : Module.Basis (Fin n) k A) (g : (R ⊗[k] A)ˣ), IsReg c b g ∧ cp (matU b g) = P

def GramBasic : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 →
    (∀ s z, ct c (mat b z) * gramL b s = gramL b (io c A z * s) ∧ gramL b s * mat b z = gramL b (s * z) ∧
      ct c (gramL b s) = gramL b (io c A s) ∧ (gramL b s).det = Algebra.norm R s * (gram R b 1).det) ∧
    (∀ x : A, gram R b x = (Matrix.of fun i j => Algebra.trace k A (x * (b i * b j))).map (algebraMap k R) ∧
      (gram R b x).det = algebraMap k R (Algebra.norm k x) * (gram R b 1).det) ∧
    ∀ g, IsReg c b g → IsUnit (gram R b (1 : A)).det ∧ Function.Injective (gramL (R := R) b) ∧
      ∀ y : Matrix (Fin n) (Fin n) R, y * mat b g = mat b g * y → ∃ z, y = mat b z

def TBase : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∃ w : (R ⊗[k] A)ˣ, io c A w.val = g.val * w.val

def TClass : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∀ w : (R ⊗[k] A)ˣ, io c A w.val = g.val * w.val →
    ∀ d : GL (Fin n) R, cp (d * th c d) = cp (matU b g) →
    ∃ (x : Aˣ) (y : GL (Fin n) R), ((thConj c y d)⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)

def TIso : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∀ w : (R ⊗[k] A)ˣ, io c A w.val = g.val * w.val →
    (∀ x : Aˣ, ∃ d : GL (Fin n) R, (d⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)) ∧
    ∀ (x x' : Aˣ) (d d' : GL (Fin n) R), (d⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) →
      (d'⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x' : A)) * w.val) → d * th c d = matU b g ∧
      ∀ y, d' = thConj c y d ↔ ∃ z : (R ⊗[k] A)ˣ, y = matU b z ∧ (1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A) = z * io c A z

end UpperTheory.ConvolutionTheory.D
