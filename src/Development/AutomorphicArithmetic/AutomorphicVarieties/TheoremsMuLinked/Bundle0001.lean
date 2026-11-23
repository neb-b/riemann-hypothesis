module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.CuspRep

namespace UpperTheory.V.Th

def Unl (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ} (M : ℕ)
    (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ κ, Af.FlagAt M m r A κ ∧ ∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def AutP {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ Af.AttC ι r π

end UpperTheory.V.Th

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Number
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Alg

namespace UpperTheory.V.Th


open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws in
def SpPt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), Ctx2 D ∨ Ctx3 D →
    ∀ r, D.EPt r → Irr r → ∃ T : Tower D, T.Fit ∧ T.Deep ∧ ∀ c₁ : Coef l,
      ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l)
        (r₁ : G ℚ Ω →* M4 (PadicAlgCl l)), c₁.O ≤ c'.O ∧ IsConj4 r r₁ ∧ D.Mult r₁ ∧
        r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r ∧
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) ∧ Irr (r₁.comp T.L.fixingSubgroup.subtype)

end UpperTheory.V.Th

end
end

