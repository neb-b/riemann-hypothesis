module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

def Framed (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam : D.host.E, μ ≠ 0 ∧ (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧
    (∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) ∧
    (∀ k (a : Fin D.R.rS), B.d.e k a = μ * lam ^ (D.R.rS - (a : ℕ)) * X.ιE (X.eR a (Fin.cast (rank_eq X h) k))) ∧
    ∀ k (a : Fin D.R.rS), B.d.e' k a = (star (μ * lam ^ (D.R.rS - (a : ℕ))))⁻¹ * X.ιE (X.fR a (Fin.cast (rank_eq X h) k))

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
section
noncomputable section
open Formalism.BasicNotions GlobalTheory.SeeSaw GlobalTheory.QPl
namespace GlobalTheory.QTw
variable {D : D7} {c : Comm D} {t : Tup c}

def resc (w : VTup t) (s : ∀ j, t.Ch j → ℂ) : VTup t :=
  { w with
    dQ := fun j α γ => (s j α * (s (j + 1) γ)⁻¹) • w.dQ j α γ
    ε := fun j α => s j α • w.ε j α
    εT := fun n h β => s n β • w.εT n h β }

def QPinU (v : VCom c) (w : VTup t) : Prop :=
  ∃ (w₀ : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ QPin v w₀ ∧ w = resc w₀ s

end GlobalTheory.QTw
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) {a : XGeo D}

def LocX.Red {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) (x : S.P.J)
    (g : GL (Fin D.R.r) (kP PP)) : Prop :=
  ∀ (i j : Fin D.R.k ⊕ Fin (l.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ j → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val i j - (ofSplit l.q).pr (z : D.host.E)) < 1

structure SymRead (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k) : Prop where
  char : ∀ PP, (ofSplit (l PP).q).IsChar (pk W).ψ (S PP).ψ
  mu : ∀ PP j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ ((S PP).μ j)
  grp : ∀ g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1), g ∈ (lvP W).H ↔ ∀ PP, ∃ x, (l PP).Red (S PP) x (g PP)
  chr : ∀ (g : ∀ PP : (pk W).Pg, GL (Fin D.R.r) (kP PP.1)) (hg : g ∈ (lvP W).H) (x : ∀ PP, (S PP).P.J),
    (∀ PP, (l PP).Red (S PP) (x PP) (g PP)) → (lvP W).chi ⟨g, hg⟩ = ∏ PP, (S PP).P.lam (x PP)

end GlobalTheory.Fam

end
end

