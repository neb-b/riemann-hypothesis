module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Model

variable {D : D7}

abbrev nLine (D : D7) : HSp D := GlobalTheory.Doubling.hneg (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1)

theorem isLineVec_nLine {c : D.host.E} (hc : c ≠ 0) : IsLineVec (nLine D) (fun _ => c) := by
  refine ⟨rfl, ?_⟩
  have h : ∀ i j : Fin 1, (nLine D).gram i j = -1 := fun i j => by
    show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
    rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
    simp [Examples₂.sgn]
  change ∑ i : Fin 1, star c * ∑ j : Fin 1, (nLine D).gram i j * c ≠ 0
  simp [h, hc]

open GlobalTheory.ChainOnto (Com PiLocalization₂)


end GlobalTheory.SeeSaw.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsStage
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def comL (L : LevCh D Unit) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (P : LevelP L.Pg D.R.r ℂ) : Com D :=
  ⟨θ, ψ, L.mu (), L.eta, L.Pg, P, L.chi⟩

theorem mem_S {L : LevCh D Unit} (hL : L.Is ()) (θ ψ P) (k : Fin 2) (Q : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ (comL L θ ψ P).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k Q hk with h1 | ⟨Q', h1, hc⟩
  · exact ⟨Q, (hL.Pg Q).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨Q', (hL.Pg Q').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ Q'.asIdeal ↔ algebraMap _ _ x ∈ Q.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

end GlobalTheory.ChainOnto.Model

end
end

