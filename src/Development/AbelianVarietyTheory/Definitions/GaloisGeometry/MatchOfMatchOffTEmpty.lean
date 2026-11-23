module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def NonSplitSet (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w ∈ T, ¬ IsSplitAt w

def GoodOffT (l : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ (w ∉ T → ∃ B, (CG.mk π).HasSat w B)

def ScopeOffT (l : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) : Prop :=
  (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.PolarizedPair π (quadChar E ^ a) ∧ GoodOffT l T π

structure MatchOffT (U : Submodule ℂ (UA E a → ℂ)) (π : CuspSub E a) (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop where
  aut : IsAutRepU U
  unram : ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w
  split : ∀ w, IsSplitAt w → ∀ σ, π.IsLocComp w σ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ
  inf : ∀ τ lam, HasWeightAt U τ lam → (CG.mk π).infChar τ = infOfWeight lam

def DescOffT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), l.Prime → 1 ≤ a → ∀ π : CuspSub E a,
    InScope .csd l π (quadChar E ^ a) → ∀ Z : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T ∧ Disjoint T Z ∧
      ∃ U : Submodule ℂ (UA E a → ℂ), MatchOffT U π T

theorem nonSplitSet_empty : NonSplitSet (∅ : Finset (HeightOneSpectrum (𝓞 E))) := by
  intro w hw
  simp at hw

theorem matchOffT_of_match {U : Submodule ℂ (UA E a → ℂ)} {π : CuspSub E a} (h : Match U π)
    (T : Finset (HeightOneSpectrum (𝓞 E))) : MatchOffT U π T :=
  ⟨h.aut, fun w hw _ => h.unram w hw, h.split, h.inf⟩

theorem descOffT_of_desc (h : Desc) : DescOffT := by
  intro E _ _ _ l a hl ha π hπ Z
  obtain ⟨U, hU⟩ := h E l a hl ha π hπ
  exact ⟨∅, nonSplitSet_empty, Finset.disjoint_empty_left Z, U, matchOffT_of_match hU ∅⟩

end GlobalTheory.Cong

end
