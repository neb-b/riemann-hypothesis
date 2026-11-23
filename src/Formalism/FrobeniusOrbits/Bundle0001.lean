module

public import Formalism.FrobeniusOrbits.Statement

@[expose] public section

-- bundled from Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
section
open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def HostEmb : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ φ₀ : hostE ζ a b →+* ℂ,
    Function.Bijective
      (fun σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => φ₀.comp (σ : hostE ζ a b →+* hostE ζ a b))

def HostClasses : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ σ P →
    (((galE e ζ a b σ).1 = 1 ∨ (galE e ζ a b σ).1 = (-1, 1)) ↔ jacobiSym (-(d : ℤ)) p = 1) ∧
    ((galE e ζ a b σ).1 = (1, -1) ↔
      (jacobiSym (-(d : ℤ)) p = -1 ∧ jacobiSym (-(q : ℤ)) p = 1)) ∧
    ((galE e ζ a b σ).1 = c0 ↔
      (jacobiSym (-(d : ℤ)) p = -1 ∧ jacobiSym (-(q : ℤ)) p = -1))

def HostOrdersFrob : Prop :=
  ∀ e : ℕ, ∀ g : GG e,
    orderOf g.2 ∣ orderOf g ∧ orderOf g ∣ 2 * orderOf g.2 ∧
    ∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ), ((u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) →
      g.2 = hcl e u → orderOf g ≤ 2 ^ j →
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1)

def DiscrMaximalRealCyclotomic : Prop :=
  ∀ (e : ℕ) (L : Type) [Field L] [NumberField L] (ζ : L), IsPrimitiveRoot ζ (2 ^ (e + 2)) →
    discr (F1 ζ) = 2 ^ (2 ^ e * (e + 1) - 1)

def HostDiscr : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    discr (hostE ζ a b) = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) ∧
    discr (hostF ζ a b) = 2 ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) ∧
    discr (hostE ζ a b) = discr (hostF ζ a b) ^ 2 ∧
    (|(discr (hostE ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 2) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d)) ∧
    (|(discr (hostF ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 1) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d))

def HostPartner : Prop :=
  ∀ (e : ℕ) (τ : GG e), τ ∈ Psi e →
    Set.BijOn (fun g : GG e => cc e * g * τ) {g | g ∉ Psi e} (Psi e : Set (GG e))

def chC (e : ℕ) : GG e →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (chD e)


open scoped Classical in
open Classical in
def HostCharSum : Prop :=
  ∀ e : ℕ,
    (∀ χ : GG e →* ℂˣ,
      (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e), starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        if χ = 1 then (2 ^ (e + 1) : ℂ) else if χ = chC e then -(2 ^ (e + 1) : ℂ) else 0) ∧
    ∀ g : GG e,
      4 * (if g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
        (1 - ((chD e g : ℤˣ) : ℤ)) * (1 + ((chQ e g : ℤˣ) : ℤ))

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.HostDiffSupport
section
open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def KinE {L : Type*} [Field L] [Algebra ℚ L] (ζ a b : L) : IntermediateField ℚ (hostE ζ a b) :=
  ℚ⟮bE ζ a b⟯

def HostDiffSupport : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime →
    P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) →
      ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∈ P ∨ ((q : ℤ) : 𝓞 (hostE ζ a b)) ∈ P

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.HostOrbitsPlaces
section
open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def HostOrbits : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) →
    (∀ τ ∈ Psi e, ∀ i : ℕ, φ ^ i * τ ∈ Psi e ↔ Even i) ∧
    (φ.1 = c0 → φ.2 ≠ 1 → Even (orderOf φ.2) ∧ orderOf φ = orderOf φ.2)

def placeOf {e : ℕ} (g : GG e) : GG e := if g.1.2 = 1 then g else cc e * g

def HostOrbitsPlaces : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) → ∀ τ ∈ Psi e, ∀ i : ℕ,
    (placeOf (φ ^ i * τ)).2 = φ.2 ^ i * τ.2 ∧
    (φ.1 = c0 → (placeOf (φ ^ i * τ)).1 = τ.1) ∧
    (φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (φ ^ i * τ)).1 = (if Even i then 1 else (sg e).1) * τ.1)

def HostOrbitCount : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = c0 → ∀ τ ∈ Psi e,
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ.2

def HostFiniteOrder : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → ∀ M : Matrix (Fin k) (Fin k) (hostE ζ a b), M ^ g = 1 → M ≠ 1 →
    g - 1 ≤ 2 ^ (e + 2) * k

end Formalism.FrobeniusOrbits
end
end

