module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.JeigRFinite
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ClsFin
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem rl_levels (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (h1 : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (h2 : IsOpen (K₂ : Set (GL (Fin b) (Af E)))) :
    Levels E (rlΘ₁ hR E a b Ma Mb K₁ K₂) ∧ Levels E (rlΘ₂ hR E a b Ma Mb K₁ K₂) :=
  (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1 a b Ma Mb K₁ K₂ h1 h2

theorem rl_ktypes (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) : KTypes E (rlΩ₁ hR E a b Ma Mb) ∧ KTypes E (rlΩ₂ hR E a b Ma Mb) :=
  ⟨((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.1,
    ((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.2.1⟩

theorem cls_fin (hFS : FinStrict) (hCP : CandParts)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (i : F₀.C.ι)
    (h1 : IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))))
    (h2 : IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
      F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
  have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ h1 h2
  have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
  obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
  obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
  refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
  have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
  have hm := LemDd.cand_sum hc
  exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigFin
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical TensorProduct

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem eig_abs (hII : IsoInv) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (w : Pl E)
    (ϖ : (w.adicCompletion E)ˣ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (τ₁ : Representation ℂ (GLw a w) X) (τ₂ : Representation ℂ (GLw b w) Y) (h₁ : IsAdmissible τ₁) (h₂ : IsAdmissible τ₂) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧
      ∀ (X' Y' : Type) [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
        (ρ₁ : Representation ℂ (GLw a w) X') (ρ₂ : Representation ℂ (GLw b w) Y'), Nonempty (ρ₁.Equiv τ₁) → Nonempty (ρ₂.Equiv τ₂) →
        Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) (I2 a b w)) ≤ m ∧
          ∀ ξa ξb, Ev.JEigR w (GlobalTheory.SmGL.extTensor ρ₁ ρ₂) ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  haveI : FiniteDimensional ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)) :=
    _root_.GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor _ _ _ _ τ₁ τ₂ _ _
      (h₁.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
      (h₂.2 _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori _ _) (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _))
  refine ⟨_, Module.finrank ℂ (fixed (GlobalTheory.SmGL.extTensor τ₁ τ₂) (I2 a b w)), Ev.jeigR_finite w (GlobalTheory.SmGL.extTensor τ₁ τ₂) ϖ, ?_⟩
  rintro X' Y' _ _ _ _ ρ₁ ρ₂ ⟨Φa⟩ ⟨Φb⟩
  have Φ : (GlobalTheory.SmGL.extTensor ρ₁ ρ₂).Equiv (GlobalTheory.SmGL.extTensor τ₁ τ₂) := GlobalTheory.SmGL.RowOneCell.extTensorEquiv Φa Φb
  exact ⟨(hII _ _ _ _ _ ⟨Φ⟩ (I2 a b w)).2.1.le, fun ξa ξb h => Ev.jeigR_equiv Φ h⟩

theorem admissible_hecke_word_product {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (P : Pre E n) (w : Pl E) :
    IsAdmissible (prodAt P w) :=
  ⟨GlobalTheory.SmGL.isSmooth_parInd _ _, fun K ho hc => fixFin E n P w K ho hc⟩

theorem eig_one (hII : IsoInv) (hSPr : StrictProd) {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (PA : Pre E a) (PB : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) :
    ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa : Pre E a) (Pb : Pre E b), Strict Pa PA → Strict Pb PB →
      Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa Pb w ϖ ξa ξb → (ξa, ξb) ∈ Z := by
  obtain ⟨Z, m, hZ, h⟩ := eig_abs hII w ϖ (prodAt PA w) (prodAt PB w) (admissible_hecke_word_product PA w) (admissible_hecke_word_product PB w)
  refine ⟨Z, m, hZ, fun Pa Pb ha hb => ?_⟩
  have h' := h _ _ (prodAt Pa w) (prodAt Pb w) (hSPr E a Pa PA ha w) (hSPr E b Pb PB hb w)
  exact ⟨h'.1, fun ξa ξb hj => h'.2 ξa ξb hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

