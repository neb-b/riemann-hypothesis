module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc

namespace UpperTheory.V.Br

def SigP (K : Type) [Field K] [NumberField K] [IsCMField K] {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (CuspSub K n) :=
  {π | (∀ τ, π.HasInfChar τ (infOf m)) ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ HasFixed π.finPart (KLev K n M)}

def CardP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (CuspSub K n), (∀ π ∈ S, π ∈ SigP K m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def CharConj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Module.finrank ℚ F = 1 → ∀ (χ : HChar F) (a : (F →+* ℂ) → ℤ), IsAlgPos χ a → ∀ σ : ℂ ≃+* ℂ,
    ∃ χ' : HChar F, (∀ v, χ'.locInf v (-1) = χ.locInf v (-1)) ∧
      ∀ w, χ.UnrAt w → χ'.UnrAt w ∧ ((χ'.val w : ℂˣ) : ℂ) = σ ((χ.val w : ℂˣ) : ℂ)

def SatOfPol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy P ψ →
    ∀ w : HeightOneSpectrum (𝓞 E), ψ.UnrAt w → ∀ B B', (CG.mk P).HasSat w B → (CG.mk P).HasSat (cPl w) B' →
      B'.map (·⁻¹) = B.map (· * (ψ.val w)⁻¹)

def ConjP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigP K m M, ∃ π' ∈ SigP K m M, ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def IntP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigP K m M, ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M →
      ¬ (p : ℤ) ∣ discr K → ∀ B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def QuadFam : Prop :=
  ∀ N : ℕ, ∃ (K : Fin N → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, IsCMField (K i)),
    (∀ i, Module.finrank ℚ (K i) = 2) ∧ ∀ i j, i ≠ j → IsCoprime (discr (K i)) (discr (K j))

def SignNe : Prop :=
  ∀ (K K' Ω : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → IsCoprime (discr K) (discr K') →
    (res ℚ Ω K).range ≠ (res ℚ Ω K').range

def TwCard : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsIrr r → ∀ S : Finset (Γ →* kˣ),
    (∀ δ ∈ S, RepIso r (tw r δ)) → S.card ≤ n ^ 2

def ResTwo : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
    (∀ s, δ s = 1 ↔ s ∈ φ.range) → (∀ s, δ s = 1 ∨ δ s = -1) → ∀ r : Γ →* GL (Fin n) k,
    (IsIrr r → ¬ RepIso r (tw r δ) → IsIrr (r.comp φ)) ∧
    ∀ r' : Γ →* GL (Fin n) k, IsIrr (r.comp φ) → RepIso (r.comp φ) (r'.comp φ) → RepIso r r' ∨ RepIso (tw r δ) r'

def FrobEx : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)),
    (∀ B B', FrobEig ι r w B → FrobEig ι r w B' → B = B') ∧
    ∀ M : ℕ, LevelAway l M r → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ((M : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ B, FrobEig ι r w B

def RootSum : Prop :=
  ∀ (n p : ℕ), 0 < p → ∀ (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I] (q f : I → ℕ), (∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i) →
    ∀ D : ∀ i, EigData n (q i) m wt, ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2

def PotMove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω) (g : G F Ω), (∀ x, x ∈ A' ↔ g x ∈ A) → PotCrysAt r A → PotCrysAt r A'

def PotRes : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (A : ValuationSubring Ω), PotCrysAt r A → PotCrysAt (r.comp (res F Ω K)) A

end UpperTheory.V.Br
