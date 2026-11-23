module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0009
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PFrame
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem frGoodOf_holds : FRGoodOf := by
  intro h1 h2 hR E _ _ _ hE n π hπ S T F₀ F i s₁ s₂ Pa Pb D hc A G h0 hG hl he
  obtain ⟨e1, e2, e3, e4, -⟩ := F.same
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))
  obtain ⟨l1, l2, -⟩ := h2 E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP
  exact h1 E hE n (F₀.C.a i) (F₀.C.le i) π hπ F₀.μ F₀.e F₀.hμ F₀.Sec F₀.hSec F.d F.ok hP
    (fun w => (congrFun e3 w).trans (F₀.μloc w)) (fun w => by rw [e4]; exact (F₀.unif w).2)
    (fun w hw a b => (F₀.good w hw (e1 ▸ a) (e2 ▸ b)).2) (F.fam.σ F.i₀)
    (fun w hw => ⟨F.comp w hw, ((F.fam.comp F.i₀).2.2.2 w hw).2.1⟩) _ _ _ _ _ _ (F₀.A i) s₁ s₂ Pa Pb D hc l1 l2 A G h0 hG hl
    fun w hw hg k intersection_update_fsHerm_neg_one => he (⟨w, hw, hg⟩, k, intersection_update_fsHerm_neg_one)

set_option maxHeartbeats 1000000 in
theorem frWeightOf_holds : FRWeightOf := by
  intro h1 hR E _ _ _ hE n hn π hπ S F₀ d i s₁ s₂ Pa Pb D hc
  obtain ⟨G, hG, h0, -⟩ := hc.vec
  exact h1 E hE n hn π hπ F₀.μ F₀.e F₀.hμ F₀.lam F₀.hlam _ _ (F₀.C.l₁ i) (F₀.C.l₂ i) (F₀.C.inf i) s₁ s₂ Pa Pb D hc.ctx
    hc.inf₁ hc.inf₂ ⟨G, hG, h0⟩

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PLevRead
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem levReadOf_holds : LevReadOf := by
  intro hLI E _ _ _ n S d a ha hS hd hPS
  refine ⟨⟨fun w => ⟨(Rd.LevOC.locLev_oc d hd a ha w).1, (Rd.LevOC.locLev_oc d hd a ha w).2.2⟩, ?_⟩,
    ⟨fun w => ⟨(Rd.LevOC.locLev₂_oc d hd a ha w).1, (Rd.LevOC.locLev₂_oc d hd a ha w).2.2⟩, ?_⟩, ?_⟩
  · filter_upwards [Rd.levCof d a] with w hw using hw.1
  · filter_upwards [Rd.levCof d a] with w hw using hw.2
  intro W₁ W₂ G hT
  obtain ⟨⟨h1o, -⟩, ⟨h2o, -⟩, hset, -⟩ := hLI E n S d a ha hS hd hPS
  have hTU : ∀ u ∈ (lev₁ S d a).prod (lev₂ S d a), ∀ x, G (x * finH u) = G x := fun u hu x =>
    hT.1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  obtain ⟨e, -, hcp, hcp', he₁, he₂⟩ := _root_.GlobalTheory.CompanionTheory.FinActS.exists_factorEmb (E := E) a (n - a) hS
  have hlev : ∀ (i : Slot S) m, m ∈ Rd.LevOC.C d a i → e i m ∈ (lev₁ S d a).prod (lev₂ S d a) := by
    intro i m hm
    have h : e i m ∈ Rd.LevOC.gSet S d a := by
      rw [Rd.LevOC.gSet_eq]
      intro j
      by_cases hij : i = j
      · subst hij
        rw [hcp]
        exact hm
      · rw [hcp' i j m hij]
        rcases j with w | w
        · exact (d.lev a w.1).one_mem
        · exact (d.lev₂ a w.1).one_mem
    have h' : e i m ∈ (((lev₁ S d a).prod (lev₂ S d a) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) := by
      rw [hset]
      exact h
    exact h'
  refine ⟨⟨_, by rw [Subgroup.coe_prod]; exact h1o.prod h2o, hTU⟩, fun w hw => ⟨?_, fun hs => ?_⟩⟩
  · rintro ⟨m, hm⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    funext x
    have h := hTU _ (hlev (.inl ⟨w, hw⟩) m hm) x
    rw [he₁] at h
    exact h
  · rintro ⟨m, hm⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    funext x
    have h := hTU _ (hlev (.inr ⟨w, hw, hs⟩) m hm) x
    rw [he₂] at h
    exact h

end PositivityTheory.Rg.BcB.F.FG

end
end

