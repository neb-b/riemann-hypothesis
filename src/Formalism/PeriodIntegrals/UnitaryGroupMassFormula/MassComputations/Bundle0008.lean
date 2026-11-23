module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactOhat
section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Ohat

variable (F : Type) [Field F] [NumberField F]

def Ohat : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

theorem isOpen_Ohat : IsOpen (Ohat F) := by
  have h := RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => isCompact_iff_compactSpace.mp (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap (𝓕 := Filter.cofinite)
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end Ohat

end MassDataMassesW.KCptW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NVolAllOf
section
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

def FdA {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf) :
    Set ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  {n | ∃ s ∈ FdN, (splitA X.B.I.cm.sig X.B.I.J (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).1 = X.toInf hb s ∧
    (splitA X.B.I.cm.sig X.B.I.J (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).2 ∈ KX X}

def UnipotentFundamentalDomain : Prop :=
  StrongApproxN → NLevel → BridgeK → SplitIso →
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word)
    (FdN : Set X.B.I.Ginf), X.MeasTie hb → X.LevelSubgroupNormalized →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    IsFundamentalDomain (ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (FdA X hb u FdN) (X.measW u).μN

def N4 : Prop :=
  SplitIso →
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf),
    (X.measW u).IsTextNorm → X.MeasTie hb →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    (X.measW u).μN (FdA X hb u FdN) =
      X.muN u FdN * (X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))

def UnipotentCoveringCount : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word)
    (𝓕 : Set ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))),
    (X.measW u).IsTextNorm →
    IsFundamentalDomain (ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μN →
    covol (X.measW u).μN = ((X.measW u).μN 𝓕).toReal

theorem nVolAll_of (hSA : StrongApproxN) (hS : SplitIso) (h3 : UnipotentFundamentalDomain) (h4 : N4) (hc : UnipotentCoveringCount) : NVolAll := by
  intro D X hb hK u FdN hT hL hF
  have hN : (X.measW u).IsTextNorm := X.measW_norm u
  have hfd := h3 hSA NLev.nLevel_holds NBr.bridgeK_holds hS X hb hK u FdN hT hL hF
  have h4' := h4 hS X hb u FdN hN hT hF
  have hc' := hc X u _ hN hfd
  show covol (X.measW u).μN = (X.muN u FdN).toReal *
    ((X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal
  rw [hc', h4', ENNReal.toReal_mul]

end MassDataMassesW
end
end

