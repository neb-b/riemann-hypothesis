module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Published UpperTheory.V.Base

namespace UpperTheory.V.Z.Bc

section Sys

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IndSys (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) (satP : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 F)) (B + B')) ∧
    (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧
      B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 F)) B)

end Sys

def IndCh {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (e : Γ' →* Γ) (r : Γ' →* GL (Fin 2) k) (R : Γ →* GL (Fin 4) k) : Prop :=
  ∀ t : Γ, t ∉ e.range →
    (∀ g g' : Γ', e g' = t⁻¹ * e g * t → (R (e g) : Matrix (Fin 4) (Fin 4) k).charpoly =
      (r g : Matrix (Fin 2) (Fin 2) k).charpoly * (r g' : Matrix (Fin 2) (Fin 2) k).charpoly) ∧
    ∀ g : Γ', e g = t * t →
      (R t : Matrix (Fin 4) (Fin 4) k).charpoly = (r g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2)

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

def MixWt (π : TR.CuspSub E 2) : Prop :=
  ∃ (m m' : Fin 2 → ℤ) (v v' : InfinitePlace E), v ≠ v' ∧ π.HasInfChar v (infOf m) ∧ π.HasInfChar v' (infOf m') ∧
    Function.Injective ![m 0, m 1, m' 0, m' 1]

end Defs

def MixWtC (K : Type) [Field K] {M : Type} [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M] (π : CuspSub M 2) : Prop :=
  ∀ φ : K →+* ℂ, ∃ (m m' : Fin 2 → ℤ) (τ τ' : M →+* ℂ), τ ≠ τ' ∧ τ.comp (algebraMap K M) = φ ∧ τ'.comp (algebraMap K M) = φ ∧
    π.HasInfChar τ (infOf m) ∧ π.HasInfChar τ' (infOf m') ∧ Function.Injective ![m 0, m 1, m' 0, m' 1]

def IndAutC : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω], Module.finrank K M = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : CuspSub M 2) (r : G M Ω →* GL (Fin 2) (Qbar l)), AttC ι r π → MixWtC K π →
    ∀ R : G K Ω →* GL (Fin 4) (Qbar l), IsSSRep R → IndCh (galEmb K M Ω) r R → IsAutC ι R

def UpQuadI : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (r : G F Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub F 2), Continuous r → π.IsRegAlg → AttR ι r π →
      IsIrr (r.comp (galEmb F E Ω)) → ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
        ∀ (τ : E →+* ℂ) m, π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m

def UpSolI : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub F 2), Continuous r → (CG.mk π).IsRegAlg → AttC ι r π →
      IsIrr (r.comp (galEmb F E Ω)) → ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
        ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m

def AttInd : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin 2) (Qbar l)) (R : G F Ω →* GL (Fin 4) (Qbar l)) sat satP, (∀ w B B', sat w B → sat w B' → B = B') →
    (∀ w B B', satP w B → satP w B' → B = B') → AttachedSys ι r sat → IndSys (F := F) (E := E) sat satP → IsSSRep R →
    IndCh (galEmb F E Ω) r R → AttachedSys ι (tw R (cycBar F Ω l)⁻¹) satP

end UpperTheory.V.Z.Bc

end
