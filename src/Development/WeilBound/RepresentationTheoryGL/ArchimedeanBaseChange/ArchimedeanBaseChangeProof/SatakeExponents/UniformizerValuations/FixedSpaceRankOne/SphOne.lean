module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.FinrankFixedEqOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_conj_KL_ne_zero (n : ℕ) (w : Pl E) (g : UL n w) :
    ((KL n w).map (MulAut.conj g).toMonoidHom).relIndex (KL n w) ≠ 0 := by
  have hK : IsCompact (KL n w : Set (UL n w)) := GlobalTheory.LocFinU.isCompact_KL n w
  have hKo : IsOpen (KL n w : Set (UL n w)) := GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w
  have hH : IsOpen (((KL n w).map (MulAut.conj g).toMonoidHom : Subgroup (UL n w)) : Set (UL n w)) := by
    rw [GlobalTheory.LocFinU.conj_map_eq]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hKo
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hH hK

theorem gelPair_split (n : ℕ) (w : Pl E) (hw : IsSplitAt w) : GelPair (KL n w) := by
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact Subgroup.mem_top x
  refine ⟨relIndex_conj_KL_ne_zero n w, fun g => ⟨Formalism.UG.P.heckecomm_tr g.1, hmem _⟩, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)
  · intro a
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1)
  · intro g
    obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨a, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2, Subtype.ext e⟩
  · intro k hk
    exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) k.1 (Subgroup.mem_subgroupOf.1 hk))

theorem gelPair_inert (hE : Unr E) (n : ℕ) (w : Pl E) (hw : ¬ IsSplitAt w) : GelPair (KL n w) :=
  ⟨relIndex_conj_KL_ne_zero n w, fun g => g⁻¹, fun a b => mul_inv_rev a b, fun a => inv_inv a,
    fun g => _root_.GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset E hE w hw n g, fun _ hk => (KL n w).inv_mem hk⟩

theorem gelPair_KL (hE : Unr E) (n : ℕ) (w : Pl E) : GelPair (KL n w) := by
  by_cases hw : IsSplitAt w
  · exact gelPair_split n w hw
  · exact gelPair_inert hE n w hw

end PositivityTheory.Rg.BcB.F.EigA

end
