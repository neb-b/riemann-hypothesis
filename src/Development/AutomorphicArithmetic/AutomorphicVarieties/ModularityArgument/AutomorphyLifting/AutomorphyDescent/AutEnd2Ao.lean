module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V.Z.Win UpperTheory.GalN.V UpperTheory.V.Base

namespace UpperTheory.V.Z.Win.Dn

def AutEnd2C {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* UpperTheory.V.U3.GG (m := 3) (R := A)),
    UpperTheory.V.Pr.OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W

def AutEnd2Ao {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* UpperTheory.V.U3.GG (m := 3) (R := A)),
    UpperTheory.V.Pr.OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W

end UpperTheory.V.Z.Win.Dn
