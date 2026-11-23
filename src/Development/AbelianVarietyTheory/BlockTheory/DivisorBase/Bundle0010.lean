module

public import Mathlib
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

section OnePrime

variable {g : ℕ} [Fact g.Prime]

def rootC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def labelChar (ω : Fbar g →*₀ ℂ) (d : ℕ) (x y : Fbar g) : ℂ :=
  ω x ^ sInf {a : ℕ | ω y = rootC (g ^ d - 1) ^ a}


open Classical in
def cuspVal (ω : Fbar g →*₀ ℂ) (x : Fbar g) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) : ℂ :=
  if ∃ (p : (ZMod g)[X]) (k : ℕ), Irreducible p ∧ M.charpoly = p ^ k then
    (-1) ^ (Fintype.card ι - 1) *
      ∑ y ∈ (rootsBar M.charpoly).toFinset, labelChar ω (Fintype.card ι) x y *
        ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) y)),
          (1 - (g : ℂ) ^ ((rootsBar M.charpoly).toFinset.card * i))
  else 0

def IsTameLabel (ω : Fbar g →*₀ ℂ) (η : (ZMod g)ˣ → ℂ) (c : (ZMod g)ˣ) : Prop :=
  ∀ z : (ZMod g)ˣ, η z =
    labelChar ω 1 (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) (algebraMap (ZMod g) (Fbar g) (z : ZMod g))

end OnePrime

section BothPrimes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}

variable [∀ i, Fact (gp i).Prime] {K : Type} [Field K]

end BothPrimes

end GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalInducedCharacter
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

def IsCuspIndChar {F : Type} [Field F] {r : ℕ} (θ : GL (Fin r) F → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (σ : Representation ℂ (blockTri (κ := F) b) V),
    IsCuspDatum b σ ∧ ∀ g : GL (Fin r) F, θ g = LinearMap.trace ℂ _ (parInd b σ g)

abbrev kField {E : Type} [Field E] [NumberField E] (PP : Pl E) : Field (kP PP) :=
  Ideal.Quotient.field PP.asIdeal

def IsCuspIndProdChar {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsCuspIndChar (kP PP.1) (kField PP.1) r (θ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) = ∏ PP : ↥Pg, θ PP (g PP)

theorem finite_boundedLevelClassGroupFamily {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  haveI : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : ∀ PP : ↥Pg, Finite (GL (Fin r) (kP PP.1)) := fun PP => inferInstance
  exact Pi.finite

abbrev fintypeH {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [CommRing K]
    (P : LevelP Pg r K) : Fintype P.H :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  Fintype.ofFinite _

def lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  letI := fintypeH P
  ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def OneWhittakerVector : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsCuspIndProdChar Pg r s χ →
      lvlSum (P0 Pg r ψ) χ = (Nat.card (P0 Pg r ψ).H : K)

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter
end
end

