module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInf
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

abbrev GI {D : D7} (X : HidaSetting D) : Type := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J

def sect {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) : GI X := by
  classical
  exact if h : ∃ g : GI X, orbM X u' g = y then h.choose else 1

theorem sect_spec {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) (hy : ∃ g : GI X, orbM X u' g = y) :
    orbM X u' (sect X u' y) = y := by
  classical
  simp only [sect, dif_pos hy]
  exact hy.choose_spec

def kerI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (y : TupI X) : Measure (GI X) :=
  Measure.map (fun h : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) => sect X u' y * (h : GI X))
    (X.measW u').μHinf

def KerMeas : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → Measurable (kerI X u')

def HaarUniqInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ m : Measure (GI X), (∀ g : GI X, m.map (fun x => g * x) = m) → (∀ C : Set (GI X), IsCompact C → m C < ⊤) →
      ∃ c : ENNReal, c ≠ ⊤ ∧ m = c • X.measG.μGinf

def RegI : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    Measurable (orbM X u') ∧ (∀ g : GI X, Measurable (fun y : TupI X => g • y)) ∧
    (∀ g : GI X, Measurable (fun x : GI X => g * x)) ∧
    (∀ t : GI X, Measurable (fun h : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) => t * (h : GI X))) ∧
    (∀ C : Set (GI X), IsCompact C → MeasurableSet C ∧ IsCompact (orbM X u' '' C) ∧
      MeasurableSet (orbM X u' '' C)) ∧
    FbI X u' hT ⊆ Set.range (orbM X u') ∧ Set.range (orbM X u') ⊆ IndI X

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarCut
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def IsChart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (Ω : Set (HmI X)) (a : HmI X → MfI X) : Prop :=
  Ω ∈ 𝓝 (TI X u' hT) ∧ a (TI X u' hT) = 1 ∧ ContinuousAt a (TI X u' hT) ∧
    ∀ T ∈ Ω, gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _)

def PolId {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (μinf : Measure (TupI X)) (νinf : Measure (HmI X))
    (a : HmI X → MfI X) (Ω : Set (HmI X)) (c : HmI X → ENNReal) : Prop :=
  ∀ φ : TupI X → ENNReal, Measurable φ → ∀ S ⊆ Ω, MeasurableSet S →
    ∫⁻ y in gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' S) ∩ IndI X, φ y ∂μinf =
      ∫⁻ T in S, c T * ∫⁻ g, φ (g • rmulT X (a T) (Y0 X u')) ∂X.measG.μGinf ∂νinf

def SqChart : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a

end PI.AprimeInfW
end
end

