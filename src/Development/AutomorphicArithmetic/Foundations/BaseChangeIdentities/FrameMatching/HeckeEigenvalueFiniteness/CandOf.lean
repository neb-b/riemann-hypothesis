module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0004

@[expose] public section

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

theorem all_parts (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (T' : Finset (Pl E))
    (hO : ∀ i : F₀.C.ι, IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))) ∧
      IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    (∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j)) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  have hfin (i : F₀.C.ι) :
      ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
        F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
    have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ (hO i).1 (hO i).2
    have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
    obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
    obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
    refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
    have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
    have hm := LemDd.cand_sum hc
    exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩
  choose kA kB PA PB hcls using hfin
  have h1 := part1 hII hSPr F₀ d kA kB PA PB hcls T'
  exact ⟨h1.1, part2 hSPr hSJ hII hAd F₀ d kA kB PA PB hcls, h1.2⟩

theorem candFin_of (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts)
    (hLO : LevOpen) (hII : IsoInv) (hAd : AdmProd) : CandFin := by
  intro hR E _ _ _ hU n hn π hπ S F₀ T' c e b hT'
  have hO := fun i : F₀.C.ι => hLO hR E n π S F₀ T' c e b (F₀.C.a i) (F₀.C.le i)
  exact all_parts hFS hSPr hSJ hCP hII hAd F₀ (F₀.loc T' c e b) T' hO

end UpperTheory.HeckeLevelFrameExistence.CF

end
