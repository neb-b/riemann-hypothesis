module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwNonPos
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem pE_shift (a r : ℕ) (c w : ℂ) :
    pE E a r (c + w * r * (Module.finrank ℚ E : ℂ)) = pE E a r c + w.re * r := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast this.ne'
  unfold pE
  have e : (c + w * r * (Module.finrank ℚ E : ℂ)).re = c.re + w.re * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  rw [e]
  field_simp
  ring

theorem nonPos_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (w : ℂ) (haut : ∀ φ ∈ V, IsAutForm φ)
    (hV : ∀ φ ∈ V, ∀ r, 0 < r → r < a → ∀ c ∈ Exp r φ.1, pE E a r c + w.re * r ≤ 0) :
    SpectralAccumulation.NonPos (tw V w) := by
  intro φ hφ r hr hra c hc
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h0 := expTw_holds E a ψ w (haut ψ hψ) r hr hra c hc
  have h1 := hV ψ hψ r hr hra _ h0
  have e : c = (c - w * r * (Module.finrank ℚ E : ℂ)) + w * r * (Module.finrank ℚ E : ℂ) := by ring
  rw [e, pE_shift]
  exact h1

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
section
noncomputable section

open NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

def ExpDec {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (r : ℕ) (F : GA E N → ℂ) : Prop :=
  ∃ (C : Finset ℂ) (G : ℂ → GA E N → ℂ), F = ∑ c ∈ C, G c ∧
    ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E N r t * g) = Complex.exp (c * t) * G c g

def NoLog : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N r : ℕ) (ψ : Sm E N), IsAutForm ψ →
  (∀ (t : ℝ) g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
  (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup) → 0 < r → r < N →
  ExpDec r (An.ctn r ψ.1)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end

