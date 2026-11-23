module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

abbrev Levels (E : Type) [Field E] [NumberField E] (a : ℕ) : Type :=
  ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin a) (w.adicCompletion E))

structure LocOps (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (Kw : Levels E a) (J : Type) where

  pl : J → HeightOneSpectrum (𝓞 E)
  split : ∀ j, IsSplitAt (pl j)
  away : ∀ j, ((l : ℕ) : 𝓞 E) ∉ (pl j).asIdeal

  f : ∀ j, GL (Fin a) ((pl j).adicCompletion E) →₀ ℂ
  int : ∀ j g, ‖ι.symm (f j g)‖ ≤ 1

  z : ∀ j, SmIrr (GL (Fin a) ((pl j).adicCompletion E)) → ℂ
  act : ∀ j σ, ∀ v ∈ PRep.fixed σ.ρ (Kw (pl j)), opOf σ.ρ (f j) v = z j σ • v

def SphOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ),
    (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥ → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ n : ℤ, ∃ f : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)), opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum • v

structure Up (Ω : Type) [Field Ω] (l : ℕ) {E M : Type} [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [Field M] [NumberField M]
    [IsCMField M] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {a : ℕ} (π : CuspSub E a) (π' : CuspSub M a) : Prop where
  scope : ∀ l' : ℕ, InScope .csd l' π (quadChar E ^ a) → InScope .csd l' π' (quadChar M ^ a)
  self : InScope .csd l π (quadChar E ^ a)
  inf : ∀ τ : M →+* ℂ, (CG.mk π').infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))
  weak : ∀ (l' : ℕ) [Fact l'.Prime] (ι : Qbar l' ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l')), Weak π ι r → Weak π' ι (GlobalTheory.AboveL.resTo M r)

end GlobalTheory.Cong

end
