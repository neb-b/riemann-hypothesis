module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0499

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
namespace GlobalTheory.AdForm.TransAct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Fi : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      (fun e z => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩) : ColT I l u a j) ∈ (I.fm l u a).Fi j := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  exact ⟨_root_.GlobalTheory.AdForm.TransAct.trc_val_mem I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv e,
    fun s => _root_.GlobalTheory.AdForm.trans_stab I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv e s⟩

theorem twTransAct : TwTrans' := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv
  refine ⟨_, mem_Fi I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv, fun b y => funext fun g => ?_⟩
  obtain ⟨γ, hγ, e, g', hg', κ, hκ, rfl⟩ := (_root_.GlobalTheory.ChartReps.twDat_reps I hI hP l Z u a Ch A hA j hj b).1.dec g
  obtain ⟨e, rfl⟩ := e
  let M : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ := infM θ _ (rankN (I.rec7 l Z) j hj) g'
  have hu : ∀ τ, IsUnit (M τ * y.1 τ).det := fun τ => by
    rw [Matrix.det_mul]; exact (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ).mul (y.2 τ)
  let y' : (I.chain l u a).Y j := ⟨fun τ => M τ * y.1 τ, hu⟩
  have htr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g') ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun τ => rfl
  have h1 := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj _
    (mem_Fi I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv)).2 (A.chOf j e) y γ hγ ⟨e, rfl⟩ g' hg' ⟨κ, hκ⟩ y' htr
  rw [h1, GlobalTheory.T.heckeCombination_scalarForm_keeps_adelicLaws I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv _ y γ hγ ⟨e, rfl⟩ g' hg' ⟨κ, hκ⟩ y' htr]

end GlobalTheory.AdForm.TransAct
