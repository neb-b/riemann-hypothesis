module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0050

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniOfParabolicHaarMultipleStatement
section
theorem _root_.GlobalTheory.T.fubini_of_parabolic_haar_multiple :
    CompanionTheory.RgExh.Dec.N.S.Fub2 → CompanionTheory.RgExh.Dec.N.S.Fub :=
  GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaParabolicCompactFactorizationStatement
section
open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem GlobalTheory.T.iwasawa_parabolic_compact_factorization :
    ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
      ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) :=
  GlobalTheory.CompanionTheory.UGeo.iwasawa_psub
end

