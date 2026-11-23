module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc.LgModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

variable {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd}

theorem ev_all {p : Ctx → Prop} (h : ∀ K, p K) : Ev p :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0,
    fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

def LgAt (KP : ∀ B : Base, Fr B.toPre → Prop) (Q R : V4.Slot) (K : Ctx) : Prop :=
  large₂ K fun B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem largeBaseProperty_conditional : LargeBaseCondition KP Q fun K X f T c => LgAt KP Q R K → R K X f T c :=
  ev_all fun K => by
    by_cases h : LgAt KP Q R K
    · exact large₂.imp h fun _ _ _ _ t k C W V S N G c q _ => t k C W V S N G c q
    · exact GroupRetwisting.lg_all K fun _ _ _ _ _ _ _ _ _ _ _ _ _ a => (h a).elim

theorem rowL_of_good {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : GroupRetwisting.LargeBaseConditionG KP Q R) (hr : Row (sAnd Q' R) Lk H) :
    RowL KP Q Q' Lk H := by
  obtain ⟨E, e, hH⟩ := hr
  refine ⟨_, largeBaseProperty_conditional (R := R), fun κ D O c b => Built (sAnd Q' R) Lk κ D O c b ∧ E κ D O c b,
    ((EvP.of_evGd h).and e).mono fun _ _ hk t β q c b l =>
      ⟨Built.intro hk ⟨q.1, q.2 t.1⟩ l, t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩, fun 𝒜 σ s => hH 𝒜 σ fun Fm hc => ?_⟩
  obtain ⟨κ, a, b, t⟩ := s Fm hc
  exact ⟨κ, a, b, fun x hx i => (t x hx i).2⟩

end GlobalTheory.Fc.LgModel

end
