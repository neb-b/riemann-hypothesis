module

public import Mathlib
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.FrobeniusOrbits.Bundle0001
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.GL3MeanSquares.Bundle0003

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.OrbitPointsDistinct
section
open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct

noncomputable section

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def PartnerFormula : Prop :=
  ∀ (e : ℕ) (h t : HGrp e),
    cc e * ((c0, h) : GG e) * ((1, t) : GG e) = ((1, h * t) : GG e) ∧
    cc e * ((c0, h) : GG e) * (((sg e).1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * ((1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * (((sg e).1, t) : GG e) = ((1, h * t) : GG e)

def FrobArith : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (u : (ZMod (2 ^ (e + 2)))ˣ), (u : ZMod (2 ^ (e + 2))) = (p : ZMod (2 ^ (e + 2))) →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    ((∀ x : 𝓞 (hostE ζ a b), σ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = hcl e u)) ∧
    ((∀ x : 𝓞 (hostE ζ a b), σ⁻¹ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = (hcl e u)⁻¹))






def DiffStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) =
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))

def PrincipalStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b c = cc e →
  ∀ 𝔭₂ 𝔭q : Ideal (𝓞 (KinE ζ a b)), 𝔭₂.IsPrime → 𝔭q.IsPrime →
    ((2 : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ → ((q : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭q →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧
      (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟 →
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) ∧
      𝔟 ⊔ c • 𝔟 = ⊤ ∧
      (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟) ∧
      ∀ 𝔟' : Ideal (𝓞 (hostE ζ a b)),
        differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟' * (c • 𝔟') →
        (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟' →
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) →
        𝔟' = 𝔟

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
end
end

-- bundled from Formalism.GL3MeanSquares.SignsFromTrianglesSquares
section
noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

def ImHGenusOne : Prop :=
  ∀ (d x0 x1 y0 y1 : ℝ), 0 < d →
    (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).im /
        (Real.sqrt d / 2) = x1 * y0 - x0 * y1 ∧
    2 * (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).re =
        2 * (x0 * y0 + x0 * y1 + (1 + d) / 4 * (x1 * y1)) + (x1 * y0 - x0 * y1)

def Heisenberg₂ {V : Type} [AddCommGroup V] (H : V → V → ℂ) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2)

def HeisenbergCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V),
      Heisenberg₂ H x (Heisenberg₂ H y F) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x y).im : ℂ))) * Heisenberg₂ H (x + y) F z

end Formalism.HermitianLattices.WeilRepresentation
end
end

