module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

structure Pre (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Pre.Sat (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ b : Fin D.c → Multiset ℂˣ, (∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (n := (D.N i))) ∧
    GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (b i)) ∧ ∑ i, b i = B

def Pre.Reg (D : Pre E n) : Prop := ∀ τ, ∃ lam : DomWeight n, ∑ i, D.m i τ = infOfWeight lam

def ConjPl (w u : HeightOneSpectrum (𝓞 E)) : Prop :=
  u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧ (u ≠ w ∨ ¬ IsSplitAt w)

def Pre.ThetaStable (D : Pre E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ ∀ u, ConjPl w u → D.Sat u (B.map (·⁻¹))

def Pre.cls (D : Pre E n) (i : Fin D.c) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) :=
  GlobalTheory.LocGL.IrrGL.of (D.σ i w).ρ (D.σ i w).smooth (D.σ i w).irred

def WeightEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ τ, ∃ lam, HasWeightAt π τ lam

def Strings : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → ∀ i,
  ∃ (a d : ℕ) (P : CuspSub E a), 1 ≤ a ∧ 1 ≤ d ∧ P.IsUnitary ∧ IsNormalised P ∧ ∀ P', P.Iso P' → AscEmb (D.V i) P' d

def CuspCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → D.ThetaStable →
  ∀ i (a d : ℕ) (P : CuspSub E a), 1 ≤ a → 1 ≤ d → P.IsUnitary → IsNormalised P → AscEmb (D.V i) P d → P.IsCsd

def RegAlg {N : ℕ} (n : ℕ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL V τ m ∧ m.Nodup ∧ ∀ x ∈ m, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2

def RegPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → ∀ i,
  RegAlg n (D.V i)

def LocRigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n), D.Reg → D'.Reg →
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B) →
  ∃ e : Fin D.c ≃ Fin D'.c, ∀ i w, D.cls i w = D'.cls (e i) w

def PermSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n)
  (e : Fin D.c ≃ Fin D'.c) (w : HeightOneSpectrum (𝓞 E)), (∀ i, D.cls i w = D'.cls (e i) w) →
  ∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D'.h w (D'.σ · w)) →
    GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w))

def PermSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n)
  (e : Fin D.c ≃ Fin D'.c) (w : HeightOneSpectrum (𝓞 E)), (∀ i, D.cls i w = D'.cls (e i) w) → ∀ B, D.Sat w B → D'.Sat w B

def Pre.SplitAt (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

end PositivityTheory.Rg.BcB.F

end
