module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

def StrSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a) (σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))), 1 ≤ N → IsDiscrete V →
  P.IsUnitary → IsNormalised P → AscEmb V P d → (∀ w, IsLocCompGL V w (σ w)) →
  ∀ ν : Fin d → Formalism.L2.Host.HChar E, (∀ k, (ν k).IsAbsPow (spehExp d k)) →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ b : Fin d → Multiset ℂˣ,
    (∀ k, (CG.mk (P.twist (ν k))).HasSat w (b k)) ∧ GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N)) ∧
      GlobalTheory.LFun.HasSatGL w (σ w).ρ (∑ k, b k)

def RStrings : Prop := RegPart → Strings
def RCuspCsd : Prop := GlobalTheory.Published.JacquetShalikaRigidity → StrSat → Strings → CuspCsd
def RLoc : Prop := GlobalTheory.Published.JacquetShalikaRigidity → StrSat → Strings → LocRigid

end PositivityTheory.Rg.BcB.F.Rig

end
