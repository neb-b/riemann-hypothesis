module

public import Mathlib
public import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation

@[expose] public section

namespace Formalism.HermitianLatticeCounting.ExpansionTerms

section PartA2
open Finset Real MeasureTheory NumberField

def MomentConstantBound : Prop :=
  ∀ C0 CA C1 : ℝ, 0 ≤ C0 → 0 ≤ CA → 0 ≤ C1 → ∃ C : ℝ,
    ∀ (r n : ℕ) (b bv ka T j q : ℝ), 2 ≤ b → 0 < ka → ka ≤ b ^ C0 → ka⁻¹ ≤ b ^ C0 → 1 ≤ T →
      T ≤ b ^ (C0 * (2 * (r : ℝ) + 2)) → 1 ≤ n → (n : ℝ) ≤ bv → bv ≤ b → 0 ≤ j → 0 ≤ q → j + q ≤ b →
      ((n : ℝ) * √(T * max ka ka⁻¹ ^ (2 * r) * b ^ CA) * (6 * bv) ^ (2 * r + 2)) *
          max 1 (C1 * (n : ℝ) ^ 2 * (b + j + q) / ka) ^ r ≤
        b ^ (C * (2 * (r : ℝ) + 2)) * (1 + 1 / ka) ^ (2 * r + 2)

end PartA2

section PartB2
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct

def LeadingMinorCodingsAgree : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (Z : Matrix (Fin d) (Fin d) R) (l : ℕ) (h : l ≤ d),
    leadingPrincipalMinor Z l = LeadingPrincipalMinor Z l h

def DminBridge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : Fin (r + 2)), Formalism.QuantumDeterminants.Dmin k r z z' g l = leadingPrincipalMinor (Formalism.QuantumDeterminants.Zhat k r z z' g) (l : ℕ)

def GfLeD : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    0 ≤ Formalism.QuantumDeterminants.Tz k r z → 0 ≤ Formalism.QuantumDeterminants.Tz k r z' →
      Formalism.QuantumDeterminants.Gf k r z z' g ≤ ‖Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))‖ ^ 2

noncomputable def formalDeterminantVector {V : Type*} [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {r : ℕ}
    (y f' : Fin (r + 1) → V) : V :=
  ∑ a, (Matrix.of fun a b => h (y a) (f' b)).adjugate (Fin.last r) a • y a

def DualVectorOrthogonal : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ) (y f' : Fin (r + 1) → V)
    (b : Fin (r + 1)),
    h (formalDeterminantVector h y f') (f' b) = if b = Fin.last r then (Matrix.of fun a b => h (y a) (f' b)).det else 0

noncomputable def formalDeterminantVectorOnGroup (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, (Matrix.of fun a b => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a)
    (Formalism.QuantumDeterminants.fvec k r z' b)).adjugate (Fin.last r) a • (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a)

noncomputable def N3om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if r ≤ i.val ∧ i.val ≤ r + k then
    formalDeterminantVectorOnGroup k r z z' g i +
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (formalDeterminantVectorOnGroup k r z z' g) z' / (Formalism.QuantumDeterminants.Tz k r z' : ℂ) * z' i
  else 0

def OrthogonalComplementDecomposition : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    Formalism.QuantumDeterminants.Tz k r z' ≠ 0 → ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Formalism.QuantumDeterminants.inWb k r (N3om k r z z' g) ∧
      (∀ b, Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (Formalism.QuantumDeterminants.fvec k r z' b) = 0) ∧
      ∃ co : Fin (r + 1) → ℂ, formalDeterminantVectorOnGroup k r z z' g = (∑ b, co b • Formalism.QuantumDeterminants.fvec k r z' b) + N3om k r z z' g

def DualVectorUnipotentInvariant : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      N3om k r z z' (n * g * n') = N3om k r z z' g

def DualVectorEquivariant : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      N3om k r z z' (h * g * h') = h'⁻¹ *ᵥ N3om k r z z' g

def DualVectorNormOnGroup : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z' → ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (N3om k r z z' g) =
        ((Formalism.QuantumDeterminants.Gf k r z z' g / Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) ∧
      (0 ≤ Formalism.QuantumDeterminants.Tz k r z →
        (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (N3om k r z z' g) (N3om k r z z' g)).re ≤
          ‖Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))‖ ^ 2 / Formalism.QuantumDeterminants.Tz k r z')

noncomputable def rankTwoSkewOperator {V : Type*} [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (e v x : V) : V :=
  h x v • e - h x e • v

def RankTwoSkewInNilradical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ (r : ℕ) (f : Fin (r + 1) → V) (T : ℝ),
      (∀ a b, h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0) →
      ∀ (a : Fin r) (e v : V), e - f a.castSucc ∈ Submodule.span ℂ (f '' {b | b < a.castSucc}) →
        (∀ b, b ≤ a.castSucc → h (f b) v = 0) →
        e ∈ Submodule.span ℂ (f '' {b | b ≤ a.castSucc}) ∧
        (∀ x, (∀ b : Fin r, h x (f b.castSucc) = 0) → rankTwoSkewOperator h e v x = h x v • e) ∧
        (∀ b, rankTwoSkewOperator h e v (f b) = h (f b) v • e) ∧
        (∀ b, b ≤ a.castSucc → rankTwoSkewOperator h e v (f b) = 0) ∧
        rankTwoSkewOperator h e v (f a.succ) - h (f a.succ) v • f a.castSucc ∈ Submodule.span ℂ (f '' {b | b < a.castSucc}) ∧
        rankTwoSkewOperator h e v e = 0 ∧ rankTwoSkewOperator h e v v = h v v • e

noncomputable def rankTwoSkewMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (e v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    Formalism.QuantumDeterminants.herm H (Pi.single j 1) v * e i - Formalism.QuantumDeterminants.herm H (Pi.single j 1) e * v i

def RankTwoSkewMatrixApply : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (e v x : Fin n → ℂ),
    rankTwoSkewMatrix H e v *ᵥ x = Formalism.QuantumDeterminants.herm H x v • e - Formalism.QuantumDeterminants.herm H x e • v

def RankTwoSkewConjugation : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), IsUnit H.det → ∀ g ∈ Formalism.QuantumDeterminants.UH H, ∀ e v : Fin n → ℂ,
    g⁻¹ * rankTwoSkewMatrix H e v * g = rankTwoSkewMatrix H (g⁻¹ *ᵥ e) (g⁻¹ *ᵥ v)

noncomputable def nilpotentExpSquare {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (e v : ι → ℂ) (t : ℝ) :
    Matrix ι ι ℂ :=
  1 + (t : ℂ) • rankTwoSkewMatrix H e v + ((t : ℂ) ^ 2 / 2) • (rankTwoSkewMatrix H e v * rankTwoSkewMatrix H e v)

def RankTwoNilpotentGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ (a : Fin r) (e v : Fin (2 * r + k + 1) → ℂ),
      e - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
        Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) →
      (∀ b, b ≤ a.castSucc → Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) v = 0) →
      rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v * rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v * rankTwoSkewMatrix (Formalism.QuantumDeterminants.Hpk k r) e v = 0 ∧
      (∀ s t : ℝ, nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v (s + t) =
        nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v s * nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) ∧
      ∀ t : ℝ, nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t ∈ Formalism.QuantumDeterminants.Nset k r ∧
        Formalism.QuantumDeterminants.ell k r z (nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) =
          (t : ℂ) * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) v

def CharacterDerivativeNorm : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ (a : Fin r) (e v : Fin (2 * r + k + 1) → ℂ) (ka l : ℝ),
      e - Formalism.QuantumDeterminants.fvec k r z a.castSucc ∈
        Submodule.span ℂ (Formalism.QuantumDeterminants.fvec k r z '' {b | b < a.castSucc}) →
      (∀ b, b ≤ a.castSucc → Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z b) v = 0) →
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.fvec k r z a.succ) v = -Complex.I * (l : ℂ) →
      ∀ t : ℝ, Formalism.QuantumDeterminants.psi k r z ((ka : ℂ) * Formalism.QuantumDeterminants.cStd) (nilpotentExpSquare (Formalism.QuantumDeterminants.Hpk k r) e v t) =
        Complex.exp (-(2 * (ka : ℂ) * (l : ℂ) * (t : ℂ)) * Complex.I)

def MajorantOrthogonalComponent : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (y : Fin n → V) (a : Fin n),
    ∃ u : V, u - y a ∈ Submodule.span ℂ (y '' {b | b < a}) ∧ (∀ b, b < a → inner ℂ u (y b) = 0) ∧
      ‖u‖ = majorantDistance y a ∧ inner ℂ u (y a) = ((‖u‖ ^ 2 : ℝ) : ℂ)

def SkewVectorChoice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (r : ℕ) (y : Fin (r + 1) → V) (a : Fin r), majorantDistance y a.succ ≠ 0 →
      ∃ e' v' : V, e' - y a.castSucc ∈ Submodule.span ℂ (y '' {b | b < a.castSucc}) ∧
        ‖e'‖ = majorantDistance y a.castSucc ∧ ‖v'‖ = 1 ∧ (∀ b, b ≤ a.castSucc → majorantHermitianForm θ (y b) v' = 0) ∧
        majorantHermitianForm θ (y a.succ) v' = -Complex.I * (majorantDistance y a.succ : ℂ)

def MomentPointwiseBound : Prop :=
  ∀ (V ι : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ) (x : ι → V) (P : V) (d : ℂ)
    (ka la la1 : ℝ), 0 < la → ‖d‖ = 2 * ka * la1 → d • P = ∑ i, c i • x i → ∑ i, ‖c i‖ ^ 2 ≤ 4 * la ^ 2 →
      (ka * la1 / la) ^ 2 * ‖P‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2

end PartB2

section PartC2
open Finset

end PartC2

section PartD2
open Finset

end PartD2

end Formalism.HermitianLatticeCounting.ExpansionTerms
