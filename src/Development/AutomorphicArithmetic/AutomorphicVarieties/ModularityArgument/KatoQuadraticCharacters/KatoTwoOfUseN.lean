module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoNOfKato
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0006

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Z.Kato

structure Used (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] (e N : ℕ) (θ ψ : G ℚ Ω →* (Qbar l)ˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop where
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  gen : ¬ l - 1 ∣ 2 * e
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  N_pos : 1 ≤ N
  N_even : Even N
  cop : (discr K).natAbs.Coprime N
  θ_ker : θ.ker = galOf ℚ K Ω
  θ_sq : ∀ g, θ g ^ 2 = 1
  ψ_mu : Af.KillsMu N ψ
  ψ_ord : ∃ m : ℕ, ¬ l ∣ m ∧ ∀ g, ψ g ^ m = 1
  ψ_ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A, ψ s ^ 2 = 1
  even : ∃ cc : G ℚ Ω, (∃ φ : Ω →+* ℂ, ∀ x, φ (cc x) = starRingEnd ℂ (φ x)) ∧ cycBar ℚ Ω l cc ^ (e : ℤ) * ψ cc = 1
  level : Af.Level l (N * (discr K).natAbs) ![(e : ℤ), -(e : ℤ)] W
  ord : Lit.OrdPoly (e : ℤ) (-(e : ℤ)) W
  det : ∀ g, (W g : Matrix (Fin 2) (Fin 2) (Qbar l)).det = θ g
  tr_ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A,
    (W s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace =
      ((cycBar ℚ Ω l s ^ (e : ℤ) * ψ s : (Qbar l)ˣ) : Qbar l) + (((cycBar ℚ Ω l s ^ (e : ℤ) * ψ s)⁻¹ : (Qbar l)ˣ) : Qbar l)
  red : ∀ g, ‖(W g : Matrix (Fin 2) (Fin 2) (Qbar l)).trace -
    ((θ g : Qbar l) * ((cycBar ℚ Ω l g ^ (e : ℤ) * ψ g : (Qbar l)ˣ) : Qbar l) +
      (((cycBar ℚ Ω l g ^ (e : ℤ) * ψ g)⁻¹ : (Qbar l)ˣ) : Qbar l))‖ < 1
  flag : ∃ (A : ValuationSubring Ω) (χ : G ℚ Ω →* (Qbar l)ˣ) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    (∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) ∧ Af.KillsMu l χ ∧
    Af.IsFlagOn W (Dec (F := ℚ) A) κ ∧ Ine (F := ℚ) A ≤ θ.ker ∧ ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) * χ s ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ)) * χ s
  irr : Af.IsIrr ((W.comp (galEmb ℚ K Ω)).comp (cycBar K Ω l).ker.subtype)

def KatoTwo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (e N : ℕ) (θ ψ : G ℚ Ω →* (Qbar l)ˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Used l Ω K e N θ ψ W →
    ∀ (ι : Qbar l ≃+* ℂ) (f : Af.Newform (2 * e + 1)), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) →
      Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ))

end UpperTheory.V.Z.Kato
