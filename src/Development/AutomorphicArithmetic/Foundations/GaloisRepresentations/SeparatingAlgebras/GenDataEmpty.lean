module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def HypAt (K : Subgroup (UA E a)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x ∈ locU a w, x ∈ K ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)

def SatAt (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (z : Fin a → ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧
    GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map z)

def GenAt (w : HeightOneSpectrum (𝓞 E)) (Φ : MvPolynomial (Fin a) ℂ) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ z, SatAt U w z → MvPolynomial.eval (fun i => (z i : ℂ)) Φ ≠ 0

def fixedBy (W : Wt E a) (C : Subgroup (UA E a)) : Submodule ℂ (algForms W) where
  carrier := {f | ∀ k ∈ C, ∀ v g, f.1 v (g * k) = f.1 v g}
  add_mem' hf hg k hk v g := by
    simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hf k hk v g, hg k hk v g]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c f hf k hk v g := by
    simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hf k hk v g]

theorem mem_fixedBy {W : Wt E a} {C : Subgroup (UA E a)} {f : algForms W} :
    f ∈ fixedBy W C ↔ ∀ k ∈ C, ∀ v g, f.1 v (g * k) = f.1 v g := Iff.rfl

def part (W : Wt E a) (C : Subgroup (UA E a)) (P : Submodule ℂ (UA E a → ℂ) → Prop) : Submodule ℂ (algForms W) :=
  ⨆ (π : AutSub E a) (_ : P π.V), π.finPart W ⊓ fixedBy W C

def Dense {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) (K : Subgroup (UA E a))
    (P : Submodule ℂ (UA E a → ℂ) → Prop) : Prop :=
  ∀ f ∈ fixedBy W K, ∀ ε : ℝ, 0 < ε → ∃ G ∈ part W K P, ∃ e : UA E a → ℂ, (∀ g, ‖ι.symm (e g)‖ ≤ ε) ∧
    ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g

def Negl (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (B : Submodule ℂ (UA E a → ℂ) → Prop) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ h : UA E a →₀ ℂ, (∀ g ∈ h.support, g ∈ finU (E := E) (n := a) ∧ ∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧
    (∀ g ∈ h.support, ∀ g' ∈ h.support, g⁻¹ * g' ∈ K → g = g') ∧ ∑ g ∈ h.support, ‖h g‖ ^ 2 ≤ δ ∧
    ∀ U, IsAutRepU U → B U → ∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) h φ = φ

def lev (K : Subgroup (UA E a)) (w₀ : HeightOneSpectrum (𝓞 E)) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) :
    Subgroup (UA E a) := K ⊔ (locU a w₀ ⊓ J.comap (cLoc w₀))

structure GenData (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ) : Prop where
  split : ∀ w ∈ S, IsSplitAt w
  apart : ∀ w ∈ S, Apart w w₀
  hyp : ∀ w ∈ S, HypAt K w
  ne : ∀ w ∈ S, Φ w ≠ 0

def DenseGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (W : Wt E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ), GenData w₀ K S Φ → Dense ι W K fun U => ∀ w ∈ S, GenAt w (Φ w) U

def SatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (K : Subgroup (UA E a)) (w : HeightOneSpectrum (𝓞 E)),
    IsSplitAt w → HypAt K w → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) →
    ∃ z, SatAt U w z

end UpperTheory.Gal.Gen

end
