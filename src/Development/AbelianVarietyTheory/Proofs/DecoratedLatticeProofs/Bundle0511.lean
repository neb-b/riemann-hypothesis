module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0509
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocComb

open GlobalTheory.ExportSeries

theorem ratDatum_insert (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∉ P)
    (hs : SplitSet (insert PP P)) (c : WO S T →₀ ℂ) (Ξl : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : GlobalTheory.LocMod.IsLocFac D ψ S T PP c Ξl)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank) (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀) (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀)
    (hf : IsRatDatum ψ S T (idem P) Ξ f₀ f) :
    IsRatDatum ψ S T (idem (insert PP P)) (fun γ => Ξ γ * Ξl γ) f₀ (comb ψ S T c f) := by
  obtain ⟨k, _, _, _, _, p, Y, Y', _, _, _, _, FS, FT, Ξk, hd, hat, hint, hSB, hcomb, hΞ⟩ := hloc
  have hP : SplitSet P := hs.mono (Finset.subset_insert _ _)
  have he : idem P + p.e = idem (insert PP P) := by
    rw [idem, idem, Finset.sum_insert hPP, idemAt_eq hat, add_comm]
  have hs' : IsIdemSum (idem P + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) := by
    rw [he]
    convert hs.isIdemSum
  have key := _root_.GlobalTheory.LocMod.ratDatum_comb_place D k p ψ hψ hd S T Y Y' FS FT P PP (idem P) hPP hat hP.isIdemSum hs' hint ΛS ΛT hSd hTd hSi hTi Ξ Ξk hSB c
    hcomb f₀ f h0 h1 hf
  rw [he] at key
  have hfun : (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) = fun γ => Ξ γ * Ξl γ :=
    funext fun γ => by rw [hΞ γ]
  rwa [hfun] at key

theorem ratDatum_list (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E)
    (hinj : Function.Injective PPn) (hQ : ∀ i, PPn i ∈ Q) (hdis : Disjoint P₀ Q) (hs : SplitSet (P₀ ∪ Q))
    (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ)
    (hloc : ∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hSd : IsSelfDualC S ΛS) (hTd : IsSelfDualC T ΛT) (hSi : (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (hTi : (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) (h0 : IsThetaFunO ψ S T f₀)
    (h1 : IsLatVac (heisO ψ S T) (stdHom S T) f₀) (hf : IsRatDatum ψ S T (idem P₀) Ξ f₀ f) :
    ∀ L : List (Fin n), L.Nodup →
      IsRatDatum ψ S T (idem (P₀ ∪ (L.map PPn).toFinset)) (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod) f₀
        (L.foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro L
  induction L with
  | nil =>
    intro _
    have : (fun γ => Ξ γ * (([] : List (Fin n)).map fun i => Ξl i γ).prod) = Ξ := funext fun γ => by simp
    simpa [this] using hf
  | cons i L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    have hsub : P₀ ∪ ((i :: L).map PPn).toFinset ⊆ P₀ ∪ Q := by
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact Finset.mem_union_right _ (hQ j)
    have hins : P₀ ∪ ((i :: L).map PPn).toFinset = insert (PPn i) (P₀ ∪ (L.map PPn).toFinset) := by
      rw [List.map_cons, List.toFinset_cons, Finset.union_insert]
    have hnot : PPn i ∉ P₀ ∪ (L.map PPn).toFinset := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.disjoint_left.1 hdis h (hQ i)
      · obtain ⟨j, hj, hji⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact hnd.1 (hinj hji ▸ hj)
    have step := ratDatum_insert D ψ hψ S T _ (PPn i) hnot (hins ▸ hs.mono hsub) (c i) (Ξl i) (hloc i) ΛS ΛT hSd hTd hSi hTi _ f₀ _ h0 h1
      (ih hnd.2)
    rw [← hins] at step
    have hfun : (fun γ => Ξ γ * (L.map fun i => Ξl i γ).prod * Ξl i γ) =
        fun γ => Ξ γ * ((i :: L).map fun i => Ξl i γ).prod := funext fun γ => by
      rw [List.map_cons, List.prod_cons]; ring
    rw [hfun] at step
    simpa only [List.foldr_cons] using step

theorem ratDatum_foldr_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  intro D ψ hψ S T P₀ Q n PPn hinj hQ hdis c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1 hrat e he
  have hs : SplitSet (P₀ ∪ Q) := ⟨e, he⟩
  have hQ' : ∀ i, PPn i ∈ Q := fun i => (hQ _).2 ⟨i, rfl⟩
  have hP₀ : SplitSet P₀ := hs.mono Finset.subset_union_left
  have key := ratDatum_list D ψ hψ S T P₀ Q n PPn hinj hQ' hdis hs c Ξl hloc ΛS ΛT hSd hTd hSi hTi Ξ f₀ f h0 h1
    (hrat _ hP₀.isIdemSum) (List.finRange n) (List.nodup_finRange n)
  have hset : ((List.finRange n).map PPn).toFinset = Q := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun ⟨i, hi⟩ => (hQ x).2 ⟨i, hi⟩, fun h => (hQ x).1 h⟩
  rw [hset, idem_eq he] at key
  have hfun : (fun γ => Ξ γ * ((List.finRange n).map fun i => Ξl i γ).prod) = fun γ => Ξ γ * ∏ i, Ξl i γ :=
    funext fun γ => by rw [Fin.prod_univ_def]
  rwa [hfun] at key

end GlobalTheory.LocComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactoriStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QLast v w := by
  first | exact @GlobalTheory.QLastPf.qLast_of_pin | exact GlobalTheory.QLastPf.qLast_of_pin | (intros; apply GlobalTheory.QLastPf.qLast_of_pin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawPlaceLawsGiveFiniteIntegralLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem placeLaws_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c)
    (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) →
    (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v 𝒯 t w hc hvl hv ht hp
  refine ⟨fun s => ?_, ?_, ?_⟩
  · exact GlobalTheory.T.locally_finite_of_tuple_conditions D c v (t s) (w s) hc hv (ht s) (hp s).form (hp s).off (hp s).gs (hp s).qfin
  · exact _root_.GlobalTheory.ValFin.valX D c v 𝒯 t w hc hv ht hp (GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D) (_root_.GlobalTheory.Unf.Flat.flatLaw D) (_root_.GlobalTheory.SeeSaw.biAct_all D)
  · exact _root_.GlobalTheory.SeeSawLastValue.valLast D c v 𝒯 t w hc hvl hv ht hp (GlobalTheory.Unf.LastSteps.lastLaw D) (_root_.GlobalTheory.SeeLastPf.seeLast D)
      (_root_.GlobalTheory.Unf.Flat.flatLaw D) (_root_.GlobalTheory.SeeSaw.biAct_all D)

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContractionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  first | exact @GlobalTheory.FinPl.LineVanish.vanish | exact GlobalTheory.FinPl.LineVanish.vanish | (intros; apply GlobalTheory.FinPl.LineVanish.vanish <;> assumption)
end

