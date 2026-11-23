module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigList
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Imports
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

theorem part1 (hII : IsoInv) (hSPr : StrictProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) (T' : Finset (Pl E)) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  choose Z mZ hZ using fun (i : F₀.C.ι) (w : Pl E) => eig_fin hII hSPr (PA i) (PB i) w (F₀.d₀.ϖ w)
  refine ⟨fun i w => ⟨Z i w, (hZ i w).1, fun s₁ s₂ Pa Pb D hc _ => ?_⟩,
    ⟨Finset.univ.sup fun i => T'.sup (mZ i), fun i s₁ s₂ Pa Pb D hc w hw => ?_⟩⟩
  · exact ((hZ i w).2 Pa Pb (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2).2
  · have h1 := ((hZ i w).2 Pa Pb (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2).1
    have h2 : mZ i w ≤ T'.sup (mZ i) := Finset.le_sup hw
    have h3 : T'.sup (mZ i) ≤ Finset.univ.sup fun i => T'.sup (mZ i) :=
      Finset.le_sup (f := fun i => T'.sup (mZ i)) (Finset.mem_univ i)
    exact le_trans h1 (le_trans h2 h3)

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ImportsAlt
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

def Same {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w)) (D D' : Pre E n) : Prop :=
  (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
    Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
    FiniteDimensional ℂ ↥(fixed (prodAt D' w) K)

theorem part2 (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j) := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := joins_fin hSJ F₀.μ F₀.C.a kA kB PA PB
  have hs : ∀ D D' : Pre E n, Strict D D' → Same w (F₀.d₀.K' w) D D' :=
    same_of_strict hSPr hII hAd w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨j, hj⟩ := hD i Pa Pb D hc.ctx.join (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2
  exact ⟨j, hs D (Dl j) hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end

