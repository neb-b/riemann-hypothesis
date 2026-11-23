module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

variable {D : D7}

def idxS (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def idxHp (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def idxH (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def HaarIdxLoc : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), muSv X w p = (idxS X hb w p : ℝ) * muSvpp X hb w p

def HaarIdxGlob : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, muHf X w = (idxH X hb w : ℝ) * muHfpp X hb w

def LocLevi : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), idxS X hb w p = idxHp X hb w p

def GlobProd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, idxH X hb w = ∏ p : TypX X, idxHp X hb w p

def ConjugateLevelLeMaximalCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, K2u X hb w ⊆ (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

theorem ratioH_of (h1 : HaarIdxLoc) (h2 : HaarIdxGlob) (h3 : LocLevi) (h4 : GlobProd) : RatioH := by
  intro D X hb hK hM hL w
  rw [h2 X hb hK hM hL w, h4 X hb hK hM hL w]
  simp only [h1 X hb hK hM hL w, h3 X hb hK hM hL w, Finset.prod_mul_distrib]
  push_cast
  ring

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

def CMInst : Prop :=
  ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J

def FrameStd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ T : X.B.I.F,
    (frameOf X w).IsStd X.B.I.cm.sig X.B.I.J T

def LatAdapted : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ ΛX ΛW ΛY : Set (Fin X.B.I.n → X.B.I.E),
    Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) ΛX ΛW ΛY ∧
    Kf X.B.I.cm.sig X.B.I.J (ΛX ∪ ΛW ∪ ΛY) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def ProdNH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word),
    IsProdNH X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (X.measW w).μSf (X.measW w).μNf (X.measW w).μHf

def GlobFromParts : Prop := LevelSAll → CMInst → FrameStd → LatAdapted → ProdNH → GlobLevelS

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOf
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem clauses_word (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) {D : D7} (X : HidaSetting D)
    (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSv X w p = muNf X w * muHf X w ∧
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSvpp X hb w p = muNf X w * muHfpp X hb w := by
  have hne : ∏ p : TypX X, muSv X w p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hA X hb hT hL w p)
  have hS := hB X hb hT hL w
  have hR := hC X hb hK hT hL w
  refine ⟨?_, ?_⟩
  · rw [div_mul_cancel₀ _ hne, hS]
  · rw [hS, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination (-muNf X w) * hR

theorem inLevelSAt_of (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  obtain ⟨hT, hL, -, -⟩ := hH
  obtain ⟨h1, h2⟩ := clauses_word hA hB hC X hb hK hT hL u
  obtain ⟨h3, h4⟩ := clauses_word hA hB hC X hb hK hT hL u'
  exact ⟨h1, h2, h3, h4⟩

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

def KSpCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X),
    IsCompact (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

def KSpOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X),
    IsOpen (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

theorem typedNe_of (h1 : KSpCompact) (h2 : KSpOpen) : TypedNe := by
  intro D X hb _ _ w p
  have hH : ((X.measW w).μSv p.1).IsHaarMeasure := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  have hne : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))).Nonempty :=
    ⟨1, (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).one_mem⟩
  unfold muSv
  exact (ENNReal.toReal_pos (hH.toIsOpenPosMeasure.open_pos _ (h2 X w p) hne)
    (hH.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (h1 X w p)).ne).ne'

end MassDataLevelSSteps
end
end

