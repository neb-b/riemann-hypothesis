module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Formalism.SharpRestriction.GrowthBounds.Bundle0006
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
open Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pairOK_allSites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  intro j hj La La' hL hL'
  have hm : (sysS H X std).mm = D.R.m := by
    first | (rfl; done) | exact X.fl_m | exact I.fl_m
  have hjm : j + 1 ≤ D.R.m := hm ▸ hj
  have hSD0 := _root_.GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN t std J hD j (by omega) La hL
  have hSD1 := _root_.GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN t std J hD (j + 1) hjm La' hL'
  have hA : TaylorLogMetric.admitted D _ _ ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') := ⟨hSD0.1, hSD1.1, hSD0.2, hSD1.2⟩
  have hInt : ∀ x, IntOff (t.O u μ).S (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' x) :=
    fun x => _root_.GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes t std J S j La La' _
  have hK := GlobalTheory.kerTh_entire_algCoef D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (ssRec t u μ) (t.rd u μ).lev _ _ _
    (t.O u μ).S hA (_root_.GlobalTheory.TwV.sNum_lev_site t std J) hInt
  have hC := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).2 _ _ hA
  have hsp : ∀ (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i), ((sysS H X std).Pj i).IsLatTup Lb.2 → ∀ v,
      locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN i Lb) =
        ((sysS H X std).latAt v i Lb.2).map ((((J.fd std).frM i Lb v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
    intro i hi Lb hLb v
    cases i with
    | zero => exact _root_.GlobalTheory.TwV.Joint.locSp_kerN_zero t std J hD Lb hLb v
    | succ k => exact _root_.GlobalTheory.TwV.Joint.locSp_kerN_succ t std J hD k hi Lb hLb v
  refine ⟨hA, _root_.GlobalTheory.TwU.xiM_datLoc t std J S hD j hj La La' hL hL', hK.1, hK.2, _root_.GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt t std J S hD j hj La La' hL hL',
    hC.1, hC.2, fun v => ⟨?_, ?_, hsp j (by omega) La hL v, hsp (j + 1) hjm La' hL' v⟩⟩
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ j La v
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ (j + 1) La' v

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleReadingEqOfRealisingPolynomial
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.G.CmpJ.PStabEq

namespace GlobalTheory.TwV.DelA

theorem castSt_K_U {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (e : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) :
    ((castSt e S).K ((castSt e S).chOf (castCls e i c))).lev.U = (S.K (S.chOf c)).lev.U := by
  subst e; rfl

theorem castSt_y {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (e : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) :
    (castSt e S).y (castCls e i c) = S.y c := by
  subst e; rfl


set_option maxHeartbeats 2000000 in
theorem rdJ_eq_of_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (V : XR ((sysS H X std).Pj (j + 1)) ℂ), (∀ d : Dec J std, RealAt d (j + 1) hj h La φ V) → rdJ I X.onCh ι j La.1 La.2 φ = MvPolynomial.map ι V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict ι j hj h La hLa φ V hR
  refine rdJ_of_isValV I X.onCh H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds ι j hj La.1 La.2 hLa φ V ?_
  intro g hg c γ hγ κ hpt z z' hz
  have hcls : IsCG (I.at' j hj).st La.1 La.2 c.1 γ :=
    ⟨_, _, c.2, g, κ, (I.at' j hj).st.eC.apply_symm_apply La.1, hg, hγ, hpt⟩
  have hc0 : clsOf (H.core j hj) La.1 La.2 = c.1 := clsOf_eq (H.core j hj) hcls
  have hclsAt : clsAt X H (j + 1) La.1 La.2 = castCls (X.onCh j hj) (j + 1) c.1 := by
    rw [clsAt_succ X H j hj, hc0]
  obtain ⟨g', hg', hpt'⟩ := _root_.GlobalTheory.TwV.DelA.ptS_isPt S hDict j hj La hLa
  have hx : Formalism.UG.bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
      (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 * κ.1 ∈
      UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ) (((I.at' j hj).st.K _).y c).2) (U_le κ.2)
  obtain ⟨κ₀, e₀, hχ₀⟩ := Formalism.L2.G.ptOne_of ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).int (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).hypP (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).bad_p ((I.at' j hj).st.eC.symm La.1).2 La.2 g g' ⟨_, hx⟩
    (J.pt std (j + 1) hj La) hg hg' hpt hpt'
  have hU : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U := by
    unfold Joint.chart
    rw [hclsAt, J.st j hj, castSt_K_U]
    exact congrArg (fun β => ((I.at' j hj).st.K β).lev.U) c.2
  have hy : ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 =
      (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 := by
    rw [hclsAt, J.st j hj, castSt_y]
    exact congrArg Subtype.val ((GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st).y_eq c).symm
  let κ' : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U := ⟨(κ * κ₀).1, by rw [hU]; exact (κ * κ₀).2⟩
  obtain ⟨d, hdγ, hdκ⟩ := _root_.GlobalTheory.TwV.DelA.dec_update S hDict j hj La hLa γ hγ κ' (by
    rw [e₀, hy]
    show _ = _ * _ * (κ.1 * κ₀.1)
    simp only [mul_assoc])
  obtain ⟨c₂, κ₂, hc₂, hκ₂, -, hiff⟩ := _root_.GlobalTheory.TwV.DelA.realAt_succ_decomp S d j hj h La hLa
  have ec : c₂ = c := Subtype.ext (castCls_inj (X.onCh j hj) (j + 1) (hc₂.trans hclsAt))
  have eκ : κ₂ = κ * κ₀ := Subtype.ext (hκ₂.trans (by rw [hdκ]))
  have key := (hiff φ V).1 (hR d) z z' (by rw [hdγ]; exact hz)
  rw [key, ec, eκ, map_mul, Units.val_mul, hχ₀, mul_one]

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MongeAmpereChartDensityIntegral
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.CharTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasSupport_rep_tw {x : IrrGL (k := k)} {s : Multiset (IrrGL (k := k))} (hx : HasSupport x.rep s) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : HasSupport (x.tw χ hχ).rep (s.map (·.tw χ hχ)) :=
  (hx.tw χ hχ).of_equiv (x.twEquiv χ hχ)

theorem chars_tw {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (chars ξ hξ).map (·.tw χ hχ) = chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ := by
  simp only [chars, Multiset.map_map, Function.comp_def, IrrGL.tw_ofChar]

end GlobalTheory.RoadU.CharTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RallisConvOfHypotheses
section
open Formalism.BasicNotions

namespace GlobalTheory.RawLift.Assembled

theorem rallisConv_of_siegelWeil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    ∀ D : D7, GlobalTheory.RawLift.RallisConv D :=
  fun hP hW D => GlobalTheory.RawLift.rallisConv_of_steps D (GlobalTheory.SWPairProof.swPair hW D) (GlobalTheory.EisAbsPf.eisAbs hP D)
    (GlobalTheory.RawLift.kerAbs_of_cuspRapidDecay hP D) (GlobalTheory.RawLift.Move.termMove D) (GlobalTheory.TermInvProof.termInv D)
    (GlobalTheory.CuspKillProof.cuspKill_holds D)

end GlobalTheory.RawLift.Assembled
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstant
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem source_scalar_const : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj hne La
  have hW := _root_.GlobalTheory.TwV.DelA.wtOK_sites S j hj hne
  have hfr := (_root_.GlobalTheory.TwV.DelA.changed_frame_unitary S d j hj.le (rkS _ _ hW.rk) La).2.2
  obtain ⟨e, he, hmu⟩ := _root_.GlobalTheory.TwV.muT_det_ratA S j hj
  have hgd := (_root_.GlobalTheory.TwV.DelB.gMat_det S j hj.le).2 _ (d.mem j hj.le La)
  obtain ⟨q, hq⟩ := Formalism.L2.Ker.even_rankN D.R (j + 1)
  have hs : ∀ τ, (D.chTw u μ).sSharp j τ = e τ - ((D.R.N (j + 1) / 2 : ℕ) : ℤ) := by
    intro τ
    have h1 := (D.chTw u μ).sSharp_eq j hj τ
    rw [D.hcW_e u τ, ← he τ] at h1
    have h2 : D.R.N (j + 1) / 2 = q := by omega
    rw [h2]
    have h3 : ((D.R.N (j + 1) : ℕ) : ℚ) = (q : ℚ) + q := by exact_mod_cast hq
    unfold sExp' at h1
    rw [h3] at h1
    have h4 : ((D.chTw u μ).sSharp j τ : ℚ) = ((e τ - (q : ℤ) : ℤ) : ℚ) := by push_cast; rw [h1]; ring
    exact_mod_cast h4
  have hχ : d.chi j hj.le La ≠ 0 := by unfold Dec.chi; exact Units.ne_zero _
  have hcD : ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  unfold dPow sPt Dec.uS kS dPow
  rw [dite_eq_left hj.le, hmu j hj.le _ (d.mem j hj.le La), hgd.1]
  simp only []
  set n : ℤ := ((D.R.N (j + 1) / 2 : ℕ) : ℤ) with hn
  set c : ℤ := cTw D j with hc
  rw [show ∀ (A χ C B Mu P : ℂ), A * (χ * C ^ c * B) * (χ⁻¹ * Mu⁻¹ * P * C ^ (-c)) = A * B * Mu⁻¹ * P * (χ * χ⁻¹) * (C ^ c * C ^ (-c)) from
    fun _ _ _ _ _ _ => by ring]
  rw [mul_inv_cancel₀ hχ, ← zpow_add₀ hcD, add_neg_cancel, zpow_zero, mul_one, mul_one]
  rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : (embT D τ) (mM d j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hgn : (embT D τ) (d.gam j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hb := congrArg (embT D τ) hfr
  rw [map_mul] at hb
  rw [← hb, hW.sh τ, hs τ]
  show (embT D τ) _ ^ _ * _ * ((embT D τ) _ ^ _)⁻¹ * ((embT D τ) (_ * _)) ^ _ = _
  rw [map_mul]
  generalize (embT D τ) (mM d j hj.le La).1.det = m at hm ⊢
  generalize (embT D τ) (d.gam j hj.le La).1.det = g at hgn ⊢
  generalize (embT D τ) (gMat J j hj.le 1).det = G
  generalize e τ = ee
  simp only [mul_zpow, zpow_neg, zpow_sub₀ hm, zpow_sub₀ hgn, zpow_add₀ hm, zpow_add₀ hgn]
  field_simp
  ring

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem cKs_unit_indep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a a'
  have hB := _root_.GlobalTheory.TwV.DelA.uB_det_unit S hPos ι hι
  have hG := _root_.GlobalTheory.TwV.DelB.dgen_unit S ι hι
  have hD := _root_.GlobalTheory.TwV.DelB.gMat_det S
  have hL := _root_.GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one S
  have hN := _root_.GlobalTheory.TwV.prod_embT_norm_one S hPos ι hι
  have hBas := bAt_orth_lev S
  beta_reduce at hD hL hBas
  have hdPow : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (e : D.what₂.Tau → ℤ),
      (∀ τ, ‖ι (embT D τ M.det)‖ = 1) → ‖ι (dPow M e)‖ = 1 := by
    intro n M e hM
    unfold dPow
    rw [map_prod, norm_prod]
    exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hM τ, one_zpow])
  have hdPowC : ∀ (k : ℕ) (hk : k ≤ D.R.m) (c : ℤ), ‖ι (dPow (gMat J k hk 1) (fun _ => c))‖ = 1 := by
    intro k hk c
    unfold dPow
    rw [Finset.prod_zpow, map_zpow₀, norm_zpow]
    rw [show (∏ τ, embT D τ (gMat J k hk 1).det) = ∏ τ, TaylorLogMetric.embT D τ (gMat J k hk 1).det from rfl]
    rw [hN _ (hD k hk).1, one_zpow]
  have hsg : ∀ n, ‖ι (sgRev n)‖ = 1 := by
    intro n
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]
  have hcOp : ‖ι (cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    have h1 : ‖ι (sgO (sysS H X std) D (hT.gat_pos u w hg) j)‖ = 1 := by
      unfold sgO
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one (fun τ _ => ?_)
      split_ifs
      · simp [hsg]
      · simp
    have h2 : ‖ι (∏ τ, (t.O u μ).dgen τ ^ (-(szT (sysS H X std) D (hT.gat_pos u w hg) j τ)))‖ = 1 := by
      rw [map_prod, norm_prod]
      exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hG τ, one_zpow])
    unfold cOp
    rw [map_mul, norm_mul, h1, h2, one_mul]
  have hkS : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b)‖ = 1 := by
    intro b
    unfold kS
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkT : ∀ b : Lv.comp (j + 1), ‖ι (kT J j hj b)‖ = 1 := by
    intro b
    unfold kT
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkSc : ∀ b : Lv.comp j,
      ‖ι (kS J j (Nat.le_of_succ_le hj) b * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    intro b
    rw [map_mul, norm_mul, hkS, hcOp, one_mul]
  have hkSeq : ∀ b : Lv.comp j, kS J j (Nat.le_of_succ_le hj) b = kS J j (Nat.le_of_succ_le hj) a := by
    intro b
    simp only [kS, uB, (hBas j (Nat.le_of_succ_le hj) a).2 b]
  have hkTeq : ∀ b : Lv.comp (j + 1), kT J j hj b = kT J j hj a' := by
    intro b
    simp only [kT, uB, (hBas (j + 1) hj a').2 b]
  refine ⟨?_, ?_, ?_⟩
  · unfold cKs
    rw [norm_mul, norm_zpow, hL, one_zpow, mul_one, map_mul, norm_mul, map_inv₀, norm_inv, hkT, hkSc, inv_one, mul_one]
  · intro h
    have h1 := hkSc a
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  · intro b b'
    unfold cKs
    rw [hkSeq b, hkTeq b']

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuplesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_joints_hold_all_tuples : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∀ a : I.ι, GlobalTheory.TwV.JointsAt t a) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.TwU.AllTuples.joints_all_true | exact GlobalTheory.TwU.AllTuples.joints_all_true | (intros; apply GlobalTheory.TwU.AllTuples.joints_all_true <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdele
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.TwoUnits

theorem embLL_mem (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem lamC_zpow {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (zpow_mem hx n), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_zpow₀]
  congr 1

theorem lamC_inv {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (inv_mem hx), Formalism.L2.Ker.lamC_of_mem lam hx, ← map_inv₀]
  rfl

end GlobalTheory.TwV.Xc.TwoUnits


open GlobalTheory.TwV.Xc.TwoUnits in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.two_units : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hKIn hPos v π hπ j hj hcj hcj1
  have hπU : π ∈ U1 (sigD D) := hπ.1
  obtain ⟨rm, hrm⟩ := _root_.GlobalTheory.TwV.Xc.MuLL.mu_mem_LL S hD hS hKIn v π hπ j hj
  obtain ⟨ra, hra⟩ := _root_.GlobalTheory.TwV.Xc.chiI_pow_rat S hD hS j hj.le hcj π hπU
  obtain ⟨rb, hrb⟩ := _root_.GlobalTheory.TwV.Xc.chiI_pow_rat S hD hS (j + 1) hj hcj1 π hπU
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj hcj1
  have hnorm := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj hfill π hπU
  have hord : ∀ v' : (sysS H X std).Pl, ordA (A0 J) v' π = if v' = v then 1 else 0 := by
    intro v'
    split_ifs with h
    · subst h; exact hπ.2.2
    · exact ((GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) (GlobalTheory.TwV.LbB.locInt_locAt _) hS.1 v').2.2.2 v (Ne.symm h) π hπ.2.1)
  have hsum : (∑ v' : (sysS H X std).Pl, (sysS H X std).vm v' (j + 1) * ordA (A0 J) v' π) = (sysS H X std).vm v (j + 1) := by
    rw [Finset.sum_eq_single v]
    · rw [hord v, if_pos rfl, mul_one]
    · intro b _ hb; rw [hord b, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [hsum] at hnorm
  obtain ⟨𝔞, h𝔞, hχ⟩ := (_root_.GlobalTheory.TwV.Xc.chiI_hom S hD hS).2.2.2 π hπU
  have hcur := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by have := hcur.1; omega
  obtain ⟨hQ, -, hone⟩ := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ hcur.2.2.2.2.2.2.1 hp2 hcur.2.2.1 𝔞 h𝔞
  rw [← hχ] at hQ hone
  have hpK : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero)
  have hmQ : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := hrm ▸ embLL_mem D rm
  have hK : ∀ r : D.what₂.LL, S.E.iK (ex.cmp.embW u w hg r) = TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := fun r =>
    (S.hK r (embLL_mem D r)).trans (Formalism.L2.Ker.lamC_of_mem S.lam (embLL_mem D r)).symm
  refine ⟨((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ (-((sysS H X std).vm v (j + 1))) * ex.cmp.embW u w hg (rm * ra),
    ((D.what₂.places.resChar w : ℕ) : (sysS H X std).G.Kf) ^ ((sysS H X std).vm v (j + 1)) * ex.cmp.embW u w hg (rm⁻¹ * rb⁻¹), ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra, Formalism.L2.Ker.lamC_mul S.lam hmQ (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_zpow, norm_zpow, hnorm, hone, one_zpow, mul_one, ← zpow_add₀ hpK, neg_add_cancel, zpow_zero]
  · apply GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb
    show ‖S.E.iK _‖ = 1
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, Formalism.L2.Ker.lamC_mul S.lam (inv_mem hmQ) (inv_mem (zpow_mem hQ _)),
      lamC_inv S.lam hmQ, lamC_inv S.lam (zpow_mem hQ _), lamC_zpow S.lam hQ,
      norm_mul, norm_mul, norm_inv, norm_inv, norm_zpow, norm_zpow, hnorm, hone, one_zpow, inv_one, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ hpK)]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, hrm, hra]
  · show S.E.iK _ = _
    rw [map_mul, map_zpow₀, map_natCast, hK, map_mul, map_inv₀, map_inv₀, hrm, hrb, zpow_neg (chiI J π)]

end
end

