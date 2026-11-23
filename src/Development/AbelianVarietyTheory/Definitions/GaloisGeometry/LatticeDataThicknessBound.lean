module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def UnitaryAutomorphicTypeClass : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Prop

def FieldOK (E : Type) [Field E] [NumberField E] [IsCMField E] (l d : ℕ) [Fact l.Prime] : Prop :=
  ImQ E d ∧ SqAt d l ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def AutOffT (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  IsAutRepU U ∧ ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w

def SatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧
    GlobalTheory.LFun.HasSatGL w σ.ρ B

def SphOffU (w₀ : HeightOneSpectrum (𝓞 E)) (S : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → ApartAll S w → ∃ B, SatU U w B

def GenAtU (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ B, SatU U w B → Gen a (normV w) B

def CrysDRU (U : Submodule ℂ (UA E a → ℂ)) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
    IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∀ (lam : DomWeight a) (J : Multiset ℤ), HasWeightAt U (ι.toRingHom.comp τ) lam →
          J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J

def IsSysU {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (O : LocOps l ι Kw J) (U : Submodule ℂ (UA E a → ℂ))
    (θ : J → Qbar l) : Prop :=
  ∀ j (σ : SmIrr (GL (Fin a) ((O.pl j).adicCompletion E))),
    IsCompAlong U (locU a (O.pl j)) ((cLoc (O.pl j)).comp (locU a (O.pl j)).subtype) σ.ρ → θ j = ι.symm (O.z j σ)

end GlobalTheory.CongL

end
