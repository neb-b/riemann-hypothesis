module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc UpperTheory.V.Br

namespace UpperTheory.V.Lev

def IsAbPol {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (n : ℕ) (x : WD h) : Prop :=
  ∃ μ : Fin n → ↥(Weil h) →* ℂˣ, ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))

structure LevelF {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ κ, FlagAt M m r A κ

theorem LevelF.of_level {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)} (H : Level l M m r) : LevelF l M m r :=
  ⟨H.cont, H.away, fun w hw => by
    obtain ⟨A, hA, χ, κ, h1, h2, h3, -⟩ := H.above w hw
    exact ⟨A, hA, κ, χ, h1, h2, h3⟩⟩

def FlagPol : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∃ μ : Fin n → ↥(Weil h) →* ℂˣ,
        (∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s = ∏ i, (X - C (μ i s : ℂ))) ∧
        (∀ i (s : ↥(Ine (F := F) A)), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → μ i (ineIncl h s) = 1) ∧
        ∀ i j, (∀ s, (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s) →
          κ i = κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype ∨ κ j = κ i * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def UnlGap : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, FlagAt M m r A κ → (∀ i j, m i ≠ m j + 1) →
      ∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def LevelFRes : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), LevelF l M m r → LevelF l M m (r.comp (res F Ω K))

end UpperTheory.V.Lev

end
