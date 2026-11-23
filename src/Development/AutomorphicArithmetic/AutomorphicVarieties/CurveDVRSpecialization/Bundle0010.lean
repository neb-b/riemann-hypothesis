module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.marks_of_link :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    Ψ σ = 1 → Marks η Ψ σ g₁ := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ ok _ hσ hΨ
  obtain ⟨hc, ec⟩ := k.c
  obtain ⟨hg, eg⟩ := k.g0
  refine ⟨hσ, ?_, hΨ, ?_, ?_⟩
  · have h := k.del ⟨σ, hc⟩
    rw [ec, ok.del_c] at h
    exact h.symm
  · have h := k.del ⟨g₁, hg⟩
    rw [eg] at h
    exact h.symm.trans Φ.g0.2
  · have h := k.psi ⟨g₁, hg⟩
    rw [eg] at h
    have h2 := ok.baseSubgroup_spec
    rw [h] at h2
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_one, sub_ne_zero]
    intro h3
    apply h2
    ext
    rw [Units.val_pow_eq_pow_val]
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af

namespace UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)}

end

def RankTwoAutomorphyDescendsFromAbelianCMToRat : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (galEmb ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) →
    Sd.IsAutC ι (W.comp (galEmb ℚ L Ω)) → IsAutR ι W

end UpperTheory.V.Pr

end
end

