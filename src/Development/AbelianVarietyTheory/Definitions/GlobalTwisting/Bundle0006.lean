module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ClassCountBoundAtConstructedPoints
section
noncomputable section

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

def ClassCountBoundAllPoints (𝒜 : FamClass) : Prop :=
  Closed (W1 𝒜) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def ClassCountBoundAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ClassCountBoundAllPoints 𝒜

def H_jOn (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤

def JInvariantConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_jOn 𝒜

def H_la (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

def LambdaConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_la 𝒜

end GlobalTheory.Fc.R0

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.ClassTwoEntries

open GlobalTheory.Fc

def H_hInstR (𝒜 : FamClass) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∀ (x : ℝ) (_ : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank

def InstanceRankAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_hInstR 𝒜

def DivisionSecondComplementAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm

def DivisionSecondComplementAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => DivisionSecondComplementAdmissible 𝒜

end GlobalTheory.Fc.ClassTwoEntries

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
section
noncomputable section

namespace GlobalTheory.Fc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

theorem eventuallyAllScaleContexts_and_of_both {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem eventuallyAllScaleContexts_mono_of_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

def sAnd (Q R : V4.Slot) : V4.Slot := fun K X f T c => Q K X f T c ∧ R K X f T c

def LargeBaseCondition (KP : ∀ B : Base, Fr B.toPre → Prop) (Q R : V4.Slot) : Prop :=
  EvLg fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

variable {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' R R' : V4.Slot} {Bd : BdT} {Lk : LkT Bd}

theorem LargeBaseCondition.and (h : LargeBaseCondition KP Q R) (h' : LargeBaseCondition KP Q R') : LargeBaseCondition KP Q (sAnd R R') :=
  eventuallyAllScaleContexts_mono_of_imp (fun _ H => (H.1.inter H.2).imp fun _ _ _ _ t k C W V S N G c q => ⟨t.1 k C W V S N G c q, t.2 k C W V S N G c q⟩)
    (eventuallyAllScaleContexts_and_of_both h h')


variable (KP Q Q' Lk) in
def RowL (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) : Prop := ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ Row (sAnd Q' R) Lk H


variable (KP Q Q' Lk) in
def ExBL : Prop := ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk

theorem Row.strengthen {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c) (h : Row Q' Lk H) :
    Row Q Lk H := Row.map (fun _ _ _ b => b) hQ (fun _ _ _ _ _ t => t) h

theorem RowL.and {H H' : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : RowL KP Q Q' Lk H) (h' : RowL KP Q Q' Lk H') :
    RowL KP Q Q' Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ := by
  obtain ⟨R, r, h⟩ := h
  obtain ⟨R', r', h'⟩ := h'
  exact ⟨_, r.and r', (h.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.1⟩).and (h'.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩)⟩

theorem RowL.elim {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hx : ExBL KP Q Q' Lk) (h : RowL KP Q Q' Lk H) :
    ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk ∧ Row (sAnd Q' R) Lk H := by
  obtain ⟨R, r, hx⟩ := hx
  obtain ⟨R', r', h⟩ := h
  exact ⟨_, r.and r', EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) hx, h.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩⟩

theorem Row.rowL {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (r : LargeBaseCondition KP Q R) (h : Row Q' Lk H) : RowL KP Q Q' Lk H :=
  ⟨R, r, h.strengthen fun _ _ _ _ _ t => t.1⟩

theorem largeBaseProperty_true : LargeBaseCondition KP Q fun _ _ _ _ _ => True :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun _ _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩⟩⟩⟩⟩⟩

end GlobalTheory.Fc

end
end

