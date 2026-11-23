module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.AtPlace

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.InertR
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem inert_of_not_unram {π : Submodule ℂ (UA E n → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsUnramU π w)
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) :
    ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w P.ρ (GlobalTheory.LGrp.bcParam n α) := by
  intro s ϖ q hs hinv α hα
  exact absurd (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt hs hinv.2.1 hα) hw

end GlobalTheory.PfBCI

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitS
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem split_component {π : Submodule ℂ (UA E n → ℂ)} {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    {w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt w) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hsub : GlobalTheory.SmGL.IsSubquotient P.ρ (locProd h w (σ · w)))
    (hsph : IsUnramU π w → GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w (n := n)))
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) : AtPlace π h σ w P := by
  exact ⟨hsub, hsph, fun _ _ _ hconj hinv _ _ => absurd hs (GlobalTheory.BcSpehCompare.not_isSplitAt hconj hinv.2.1), fun _ => hc⟩

end GlobalTheory.PfBCI

end
end

