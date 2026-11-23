module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Reg.modelAt_and_nonempty_global_model : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 →
    (∀ la, _root_.GlobalTheory.Reg.ModelAt Xo c la) ∧
      Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) := by
  classical
  intro E _ _ _ H Dw l Xo c hpq hgood hA
  obtain ⟨hGI, hQH⟩ := _root_.GlobalTheory.Moduli.jointExistence_and_moduliScheme
  have hne : ∀ l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l') := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab at hQH
    exact fun l' => hQH E H Dw l' hpq
  let family : (l' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l' :=
    Function.update (fun l' => Classical.choice (hne l')) l Xo
  have hfam : family l = Xo := Function.update_self _ _ _
  refine ⟨fun la => ?_, ?_⟩
  · have h := _root_.GlobalTheory.Reg.modelAt_of_good_level hGI E H Dw hpq family l c la
      (fun p hp _ => hgood p hp)
    rwa [hfam] at h
  · have hGI' := hGI
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI at hGI'
    obtain ⟨Y, -, hY⟩ := hGI'.2 E H Dw hpq family
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N6 at hY
    obtain ⟨Ygl, -⟩ := hY l c hgood hA
    rw [hfam] at Ygl
    exact ⟨Ygl⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.RealPtNZOfCurveHyp
section
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


set_option maxHeartbeats 4000000 in
theorem realPtNZ_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → 0 < wL.n → ∀ (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ], RealPtNZSt h j hj hG G la hU := by
  intro D T h j hj hG hT ka wL wF G S g0 la hH hV _ hB hwL hU _
  obtain ⟨-, hbc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hany, htw, -, -⟩ := GlobalTheory.lawsFieldsSeparately
  obtain ⟨hgood, -, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have := CompFin.finite_comp (T.Q.Xo j) T.Q.c
  obtain ⟨-, -, -, hWt, -⟩ := GlobalTheory.Frames.algebraic_laws hbc _ _ _ _ (T.Q.Xo j) T.Q.c
  exact realPt_of h j hj hG G la hU hwL
    (ptOfS_of h j hj hG hany htw hT hV G hB la (GlobalTheory.SecCount.countQAtSt D T h j hj hG hT ka wL wF G S g0 la hH)) hT
    (GlobalTheory.intFrames_of_laws hbc htw _ _ _ _ (T.Q.Xo j) T.Q.c) hWt
    (GlobalTheory.Frames.modelAtSt_of_good GlobalTheory.Moduli.jointExistence_and_moduliScheme.1 GlobalTheory.Moduli.jointExistence_and_moduliScheme.2 _ _ _ _ (T.Q.Xo j) T.Q.c (hpq ▸ hr) hgood la)

end GlobalTheory
end

