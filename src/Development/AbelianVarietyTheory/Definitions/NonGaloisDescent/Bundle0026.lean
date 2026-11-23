module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLawsOfLawsLit
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.CuspModel

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_ofChar (χ ψ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) (e : ψ = χ⁻¹) :
    DualCl (IrrGL.ofChar χ hχ) (IrrGL.ofChar ψ hψ) := by
  subst e
  exact ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ⁻¹ hψ, rfl, rfl,
    ProjLine.nonempty_equiv_contra_ofChar (χ := detChar (Fin 1) χ) hχ.detChar⟩

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r rc : IrrGL (k := w.adicCompletion E) → WD h}

end GlobalTheory.LocLanglands.CuspModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GoodCusp (y : IrrGL (k := k)) : Prop :=
  y.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) ∧
    ∃ (y₀ : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), fixed y₀.rep (KOne k (Fin y₀.1)) ≠ ⊥ ∧ y = y₀.tw χ hχ)

def Good (x : IrrGL (k := k)) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, GoodCusp y

def Toral (x : IrrGL (k := k)) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, y.1 = 1

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

variable (h) in
def TypeLaw (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∀ (E' : Type) [Field E'] [NumberField E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      (rc (cls σ)).mono0 ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

structure LawsT (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop where
  dim : ∀ x, (rc x).lpDim = x.1
  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum rc l
  cusp : ∀ x, x.IsCusp → IsIrrWD (rc x)
  nu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s
  absCentral : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖
  twist : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))
  central : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, Good x → HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)
  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) →
    Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc (cls π') = (rc (cls π)).lpDual
  inj : ∀ x y, Good y → rc x = rc y → x = y
  depth : ∀ x, Good x → fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x)
  type : TypeLaw h rc


end GlobalTheory.RecT

end
end

