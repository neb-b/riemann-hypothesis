module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.TUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfP

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.BInEx
section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace CrystallineSemistableComparison.crystallineComparison

theorem bInEx : BInEx := by
  intro l _ K _ M hM j
  obtain ⟨d, hA⟩ := GlueB'.atlas_of hM
  obtain ⟨N, hN⟩ := B.main l d j
  obtain ⟨v, -, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  have ht : tA l = (GlueBE.eps l).μ * v := by rw [GlueBE.eps_μ]; exact e
  have hC := B.compat l
  have hup := fun n : ℕ =>
    (hN (B.schFn M.p) (okToOC l K) (GlueBE.eps l) hA.some n).1 true
  refine ⟨⟨2 * N, fun y => ?_, fun x hx => ?_⟩, fun x n => ?_, fun g x n => ?_⟩
  · obtain ⟨x, hx⟩ := GlueBL.lim_surj (GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) _ v (tA l) N ht hup y
    exact ⟨x, fun n => congrArg (fun z => z.1 n) hx⟩
  · exact GlueBL.lim_inj (GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) _ v (tA l) N ht hup x (Subtype.ext (funext hx))
  · exact hC.phi (B.schFn M.p) (okToOC l K) n j _
  · exact hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) true n j _

end CrystallineSemistableComparison.crystallineComparison

end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.EndExOf
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace CrystallineSemistableComparison.crystallineComparison

theorem endEx_of (hP : BocksteinBaseChangeP) : EndEx := fun hI l _ K _ =>
  have hC : Chapters := chapters_of hP
  (hP l K).elim fun Amp hA => (hC.et l K).elim fun e he =>
    (glueB l K Amp (hC.main l) (hC.compat l) (hC.c1 l)).elim fun β _ =>
      ⟨Amp, e, GlueE.emap Amp e he, he, facts l K, hI l K,
        glueL l K Amp (hC.compatH l) (hC.rin l) hC.uniq hA.1 hA.2.1, ⟨β⟩, hA.2.2.1, fun _ _ _ _ _ => rfl⟩

end CrystallineSemistableComparison.crystallineComparison

end
end

