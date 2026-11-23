module

public import Mathlib
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.GelfA
section
noncomputable section

namespace GlobalTheory.Mem.Gelf

open MvPolynomial

def rowE (R : Type) [CommRing R] (r n : ℕ) :
    Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n,
    (LinearMap.mulLeft R (X (a, s) : MvPolynomial (Fin r × Fin n) R)).comp (pderiv (R := R) (b, s)).toLinearMap

def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def gelfA {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => if a = b then μ a + ((N - 1 - a.val : ℕ) : R) else if a < b then -1 else 0

def gelfC {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R :=
  ∑ a, ∑ b, (gelfA μ ^ k) a b

end GlobalTheory.Mem.Gelf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HarmonicAllOfCompact
section
noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def fockEmb (σ : Type) [DecidableEq σ] :
    MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2 :=
  (basisMonomials σ ℂ).constr ℂ fun α =>
    lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)

theorem isFockIsometry_fockEmb (σ : Type) [DecidableEq σ] : IsFockIP (fockEmb σ) := by
  intro α β
  have h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) =
      lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro γ
    have := (basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ =>
      (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) :
        lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ
    simpa [fockEmb] using this
  rw [h, h, lp.inner_single_left]
  split_ifs with e
  · subst e
    have h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0]
    simp [Finsupp.prod]
  · rw [lp.single_apply_ne _ _ _ e, inner_zero_right]

end GlobalTheory.FockAlg.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
section
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

def valAt (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (c : C) : (Fin N → K) →ₗ[K] VV K lam :=
  ((bVV K lam).equivFun.symm : (VVIdx lam → K) →ₗ[K] VV K lam) ∘ₗ LinearMap.funLeft K K fun i => e.symm (c, i)

def sumLat (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (T : C → Submodule (𝓞 K) (VV K lam)) :
    Submodule (𝓞 K) (Fin N → K) :=
  ⨅ c, (T c).comap ((valAt lam e c).restrictScalars (𝓞 K))


open Classical in
def sumGram [StarRing K] (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (G : ι → Matrix (Fin n) (Fin n) K) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b => if (e a).1 = (e b).1 then pairK lam G (bVV K lam (e a).2) (bVV K lam (e b).2) else 0

def IsMetric (H : Matrix (Fin N) (Fin N) K) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ v : InfinitePlace K, IsUnit (X v).det ∧ ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding

def SpreadLe (lam : ι → DomWeight n) (R : ℝ) : Prop := ∀ τ i j, (((lam τ).w i - (lam τ).w j : ℤ) : ℝ) ≤ R

def IsDefGram [StarRing K] (G : Matrix (Fin n) (Fin n) K) : Prop :=
  Gᴴ = G ∧ (∀ a b, G a b ∈ Formalism.DivisionValues.cmMax K) ∧ ∀ φ : K →+* ℂ, (G.map φ).PosDef

def IsSelfDualK [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) : Prop :=
  Submodule.IsLattice K M ∧ hdualFr G M = M

def IsSelfDualE {E : Type} [Field E] [NumberField E] (cE : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Submodule.IsLattice E L ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range

def bound (f ν : ℕ) (R : ℝ) : ℝ := 4 * (f : ℝ) * ν * R * Real.log (ν * R)

end GlobalTheory.TestLat
end
end

