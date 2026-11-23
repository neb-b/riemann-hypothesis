module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

namespace GlobalTheory.HeckeGal.Model

variable (E : Type) [Field E] [NumberField E]

def absPow (s : ℝ) : HChar E :=
  ⟨GlobalTheory.Mem.Chr.CharModel.absHom E s, (GlobalTheory.Mem.Chr.CharModel.absChar E s).2⟩

theorem absPow_isAbsPow (s : ℝ) : (absPow E s).IsAbsPow s :=
  GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) s

theorem frob_abs {Ω : Type} [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {m : ℕ} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι (absPow E m) n r) {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) ^ m := by
  rw [h.frob_unr ha (Or.inl hv) ((absPow_isAbsPow E m).1 v) hA hσ, (absPow_isAbsPow E m).2.1 v,
    Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, map_inv₀, inv_inv, map_pow, map_natCast]
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.HeckeGal.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesUpqUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)

theorem discreteSeriesUpqUnique_iff : DiscreteSeriesUpqUnique ↔ GlobalTheory.Dec.DSUnique :=
  ⟨fun h n ε lam H _ _ σ H' _ _ σ' hl hσ hσ' => h n ε lam hl H H' σ σ' hσ hσ',
    fun h n ε lam hl H H' _ _ _ _ σ σ' hσ hσ' => h n ε lam H σ H' σ' hl hσ hσ'⟩

theorem discreteSeriesUpqUnique_of_classification (h : GlobalTheory.DSId.DSClass) : DiscreteSeriesUpqUnique :=
  discreteSeriesUpqUnique_iff.2 (GlobalTheory.LowestKTypeDetermines.dsUnique_of_dsClass h)

end GlobalTheory.Published
end
end

