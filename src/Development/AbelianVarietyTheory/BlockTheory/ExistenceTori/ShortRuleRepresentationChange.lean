module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

def CoverVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ThVal Δ.cov.Xo₂ Δ.cov.c₂ Δ.nab₂ y₂ Λ N (Δ.cov.incl β) (Δ.combinedCoeff x₀) a (MvPolynomial.map Δ.cov.incl P) v

def IsShortRule {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R),
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra Δ.cov.c₂.F S') (φ : p.R →+* S')
      (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'), φ.FaithfullyFlat ∧ Δ.cov.LiesOver φ y₂ y) ∧
    ∀ (S' : Type) [CommRing S'] [Algebra Δ.cov.c₂.F S'] (φ : p.R →+* S') (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'),
      Δ.cov.LiesOver φ y₂ y → ∃ v, CoverVal Δ y₂ Λ N β x₀ a P v ∧ φ (f p y) = v * Δ.fnVal y₂

def ramPart (E : Type) [Field E] [NumberField E] : ℕ := 2 * (discr E).natAbs

def reps (n : ℕ) (s : ℕ+) : Set (Lat E n) :=
  {Λ | Λ.InGenus ∧ Λ.StdAt (ramPart E * Δ.a.l₂.M * s)}

def IsPairIso {n : ℕ} (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (Λ Λ' : Lat E n) : Prop :=
  IsUnitary γ ∧ (Λ.map γ).L = Λ'.L ∧
    ∀ x ∈ Λ.L, ∃ k : ℕ, k.Coprime Δ.a.l₂.M ∧ k • (γ x - x) ∈ mulStd E n Δ.a.l₂.M

def MeetsAllClasses {n : ℕ} (T : Set (Lat E n)) : Prop :=
  T ⊆ reps Δ n 1 ∧ ∀ Λ ∈ reps Δ n 1, ∃ Λ' ∈ T, ∃ γ, IsPairIso Δ γ Λ Λ'

def IsSeriesData {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ ∈ reps Δ n 1 ∧ Λ.Admissible Δ.a.l₂.M N ∧ IsBeLat Dw c Λ β ∧ P ∈ harmLat Dw c a Λ

def shortGen (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}

def Descends : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∃ f ∈ sec Xo c a n, IsShortRule Δ Λ N β x₀ a P f

def OnePos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∃ τ : E →+* ℂ, InPsi H τ ∧ (0 < Dw.p → 1 ≤ a (τ, Dw.p - 1))

def ShortInCusp (hK : ReflexLe Dw c) (nV : ℕ)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a → ∀ f ∈ shortGen Δ hK nV a n, f ∈ cusp a n



end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
