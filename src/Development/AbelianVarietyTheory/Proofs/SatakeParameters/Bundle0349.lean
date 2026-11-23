module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormNormalisedValuesLatticeTupleStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparedForm_normalisedValues_latticeTuple : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  first | exact @GlobalTheory.TwV.DelA.cmp_valsAt | exact GlobalTheory.TwV.DelA.cmp_valsAt | (intros; apply GlobalTheory.TwV.DelA.cmp_valsAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominator
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem det_zT_ne_zero {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.mpr (hf τ)
    have e : ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := rfl
    rw [e, Matrix.det_permute', Matrix.det_transpose]
    refine mul_ne_zero (by simp [Units.ne_zero]) ?_
    intro h0
    have := Matrix.det_nonsing_inv_mul_det (f τ) hu
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact hf τ

theorem opId_denom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG s hs
  apply sub_eq_zero.mp
  apply _root_.GlobalTheory.TwV.DelA.eq_zero_of_evD_generic X D pos Kc ι j hN
  intro d f' hf hdf
  have hZ : ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) ≠ 0 := by
    rw [map_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (det_zT_ne_zero X D pos f' hf τ)
  have hL := _root_.GlobalTheory.TwV.DelA.leftSide_at_point X D pos Kc ι j hN ν hν Q hQ Gc G hR hG d f' hf hdf
  have hRr := GlobalTheory.T.transportedPolynomial_complexPoint_evaluation X D pos Kc ι j hN ν hν Q hQ s hs d f' hf
  have hc : evD X D pos ι hN d f' (cD X Kc j (ι (cOp X D pos j s))) = ι (cOp X D pos j s) := by
    simp [evD, cD]
  have hS : (∏ τ, s τ ^ (-(szT X D pos j τ))) * ∏ τ, s τ ^ szT X D pos j τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hs τ))]
  rw [map_sub, sub_eq_zero]
  apply mul_right_cancel₀ hZ
  rw [hL, (evD X D pos ι hN d f').map_mul (denD X Kc j), (evD X D pos ι hN d f').map_mul (cD X Kc j _), hc, mul_assoc ((evD X D pos ι hN d f') (denD X Kc j)), mul_assoc (ι (cOp X D pos j s)), hRr, ← ι.map_mul]
  congr 2
  unfold cOp
  linear_combination (-(sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f'))) * hS

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicDatumWithLawsAtJoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.exists_adLawAt_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ Xi muT, AdLawAt J.A J.dtU J.a Xi muT :=
  by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J
  exact ⟨_, _, _root_.GlobalTheory.TwV.adLawAt_xiAd J.A J.dtU J.a J.pins J.tie⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuples
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.oneTie_jointsAt_all : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l l0 Z L hT Gi Gl K Y cX ex t C full g nch tp _htp hTw hJ htw hpi hS hC _hLv hDt hg hgf hD hLat
  obtain ⟨t', hS', hR', _, hM'⟩ := GlobalTheory.Pdv.stdKer_stdRd_mark I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  obtain ⟨h1, h2⟩ := GlobalTheory.T.trueColumn_joints_hold_all_tuples I hOk hP l Z l0 L hT Gi Gl K Y cX ex t' C full g hTw hJ htw hpi hS' hR' hM' hC hDt hg hgf hD hLat
  exact ⟨⟨t', h1⟩, h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMove
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem site_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  intro j hj c L La' γ hL hLa'
  rw [hmm] at hj
  have hr := hN j
  obtain ⟨g, κ, hM⟩ : ∃ g κ, MoveBy std J j hj.le c L γ g κ := by
    cases j with
    | zero => exact _root_.GlobalTheory.TwV.Xc.moveBy_zero S hD hS c L γ hL
    | succ i => exact _root_.GlobalTheory.TwV.Xc.moveBy_succ S hD hS i hj.le c L γ hL
  have hU := ((GlobalTheory.TwV.Xc.eMat_unitary_det _ _ (fun _ => rfl) _ _ hr _ _ (J.pins.crd_orth j hj.le)).2 g hM.1).1
  obtain ⟨hcq, hxi⟩ := _root_.GlobalTheory.TwV.Xc.xiM_smul_moveBy S hD hS j hj c L γ g κ hr hL hM La'
  refine ⟨eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g, _, hU, ?_,
    _root_.GlobalTheory.TwV.Xc.kerN_smul S hD hS j hj c L γ g κ hr hL hM, hcq, hxi, GlobalTheory.T.latticeTupleMove_scalar_power_of_p S hD hS hPos hPair j hj c L γ g κ hr hL hM La' hLa'⟩
  intro v
  rw [_root_.GlobalTheory.TwV.Xc.frM_fd_comp S hD hS j c (((sysS H X std).Lv.lev j c).smul γ L) L]
  exact hM.2.2.1 hr v

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalfStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_site | exact GlobalTheory.TwV.DelB.delPolAt_site | (intros; apply GlobalTheory.TwV.DelB.delPolAt_site <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteScalarsAgreeAwayFromPlace
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.AwayId

theorem key {K : Type} [Field K] {P M C : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' n n' : ℤ) :
    P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
      (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n' = 1 := by
  simp only [mul_zpow, ← zpow_mul, inv_zpow', mul_sub, zpow_sub₀ hP, neg_mul, zpow_neg]
  rw [mul_comm A n, mul_comm A' n', mul_comm V n, mul_comm V n']
  field_simp

theorem map_zpow_of {G M : Type*} [Group G] [DivisionMonoid M] (f : G → M) (U : Subgroup G) (h1 : f 1 = 1)
    (hm : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x * f y) {x : G} (hx : x ∈ U) (n : ℤ) : f (x ^ n) = f x ^ n := by
  let φ : U →* M := { toFun := fun y => f y, map_one' := h1, map_mul' := fun y z => hm _ y.2 _ z.2 }
  have := map_zpow φ ⟨x, hx⟩ n
  simpa [φ] using this

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam hy, lamC_eq_of_mem lam (mul_mem hx hy), ← map_mul]
  rfl

theorem lamC_zpow' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (zpow_mem hx n), ← map_zpow₀]
  rfl

theorem lamC_inv' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (inv_mem hx), ← map_inv₀]
  rfl

theorem lamC_ne_zero' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [lamC_eq_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem final {K : Type} [Field K] {P M C Q s : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' la la' n n' : ℤ) :
    Q * P ^ (V * (n - n')) * (s * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A')) *
        ((P ^ (-V) * (M * C ^ A)) ^ (la + n) * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ (la' + n')) =
      Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') := by
  have hXa : P ^ (-V) * (M * C ^ A) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero hM (zpow_ne_zero _ hC))
  have hXb : P ^ V * (M⁻¹ * C ^ (-A')) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero (inv_ne_zero hM) (zpow_ne_zero _ hC))
  have hk := key hP hM hC V A A' n n'
  rw [zpow_add₀ hXa, zpow_add₀ hXb]
  calc _ = Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') *
        (P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
          (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n') := by ring
    _ = _ := by rw [hk, mul_one]


set_option maxHeartbeats 4000000 in
theorem scal_away : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∀ a b : (sysS H X std).G.Kf, S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) → S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))) → ∀ (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.pPow (sysS H X std) j La La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La') * S.E.iK (a ^ len (sysS H X std) v j Lb.2 * b ^ len (sysS H X std) v (j + 1) Lb'.2) = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb') * S.E.iK (a ^ len (sysS H X std) v j La.2 * b ^ len (sysS H X std) v (j + 1) La'.2)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSpl hP v π hπ j hj a b ha hb La Lb La' Lb' hab hab'
  have hR := GlobalTheory.TwV.DelB.sysS_ranks S
  have hjle : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hjm : j < (sysS H X std).mm := hR.1 ▸ hj
  have hPa := hP j hjm La La' hab.1 hab'.1
  have hPb := hP j hjm Lb Lb' hab.2.1 hab'.2.1
  obtain ⟨k, hkU, hkI, hkO, hk⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ j hjle La Lb hab
  obtain ⟨k', hkU', hkI', hkO', hk'⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ (j + 1) hj1 La' Lb' hab'
  obtain ⟨c0, hc0⟩ := _root_.GlobalTheory.TwV.Xc.chi_detId_kerN_eq S hD hSpl j hjle
  obtain ⟨c0', hc0'⟩ := _root_.GlobalTheory.TwV.Xc.chi_detId_kerN_eq S hD hSpl (j + 1) hj1
  obtain ⟨-, hsl⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v j hjle La Lb hab
  obtain ⟨-, hsl'⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v (j + 1) hj1 La' Lb' hab'
  obtain ⟨hχm, hχ1, -, hχN⟩ := _root_.GlobalTheory.TwV.Xc.chiI_hom S hD hSpl
  have hbad := (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hSpl).2.2.2
  have hdtb := (_root_.GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length S hD hSpl j hjle Lb hab.2.1).1
  have hdtb' := (_root_.GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length S hD hSpl (j + 1) hj1 Lb' hab'.2.1).1
  have law := S.law
  have hmuk : ∀ κ ∈ U1 (sigD D), κ ∈ intU D.host.F D.host.E → OneOff ((A0 J).pl v).1 κ → S.muT (j + 1) κ = 1 := by
    intro κ hκ hκI hκO
    refine law.mu_unr j hj κ hκ hκI fun v' hv' => hκO v' fun h => hbad v' hv' ?_
    rw [h]
    exact ((A0 J).pl v).2

  have hmuF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → S.muT (j + 1) κ = 1 →
      S.muT (j + 1) (x * π ^ e * κ) = S.muT (j + 1) x * S.muT (j + 1) π ^ e := by
    intro x hx e κ hκ h1
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [(law.mu_mul j hj).2 _ (mul_mem hx hpe) _ hκ, h1, mul_one, (law.mu_mul j hj).2 _ hx _ hpe,
      map_zpow_of (S.muT (j + 1)) (U1 (sigD D)) (law.mu_mul j hj).1 (law.mu_mul j hj).2 hπ.1 e]
  have hchi1 : chiI J 1 = 1 := hχ1 1 (one_mem _) (one_mem _)
  have hchF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → κ ∈ intU D.host.F D.host.E →
      chiI J (x * π ^ e * κ) = chiI J x * chiI J π ^ e := by
    intro x hx e κ hκ hκI
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [hχm _ (mul_mem hx hpe) _ hκ, hχ1 κ hκ hκI, mul_one, hχm _ hx _ hpe, map_zpow_of (chiI J) (U1 (sigD D)) hchi1 hχm hπ.1 e]
  have hscal : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' *
        (S.muT (j + 1) π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) *
          (S.muT (j + 1) π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2))⁻¹ *
          (chiI J π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2)) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          (chiI J π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2)) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
    unfold GlobalTheory.TwU.scal0
    rw [hc0 La hab.1 hPa.1.2.2.1, hc0 Lb hab.2.1 hPb.1.2.2.1, hc0' La' hab'.1 hPa.1.2.2.2, hc0' Lb' hab'.2.1 hPb.1.2.2.2, hk, hk',
      hmuF _ hdtb _ k hkU (hmuk k hkU hkI hkO), hmuF _ hdtb' _ k' hkU' (hmuk k' hkU' hkI' hkO'),
      hchF _ hdtb _ k hkU hkI, hchF _ hdtb' _ k' hkU' hkI']
    simp only [mul_zpow, mul_inv]
    ring

  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j La La' = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' *
      ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1) *
        ((len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) -
          (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2))) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have he : ∀ v' ∈ Finset.univ.erase v, (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) La'.2 - len (sysS H X std) v' j La.2) =
        (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) Lb'.2 - len (sysS H X std) v' j Lb.2) := by
      intro v' hv'
      rw [hsl v' (Finset.ne_of_mem_erase hv'), hsl' v' (Finset.ne_of_mem_erase hv')]
    rw [Finset.sum_congr rfl he]
    ring

  have hm_alg : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := law.mu_alg j hj π hπ.1
  have hm_ne : S.muT (j + 1) π ≠ 0 := law.mu_ne hj hπ.1
  obtain ⟨𝔞, hN1, hc𝔞⟩ := hχN π hπ.1
  have hgx := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hcu := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ t.χ_ok (by omega) hgx.2.1 𝔞 hN1
  have hc_alg : chiI J π ∈ TaylorLogMetric.Qbar := hc𝔞 ▸ hcu.1
  have hc_ne : chiI J π ≠ 0 := hc𝔞 ▸ hcu.2.1
  have hsb : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' ∈ TaylorLogMetric.Qbar := hPb.2.2.2.2.1
  have hLm := lamC_ne_zero' S.lam hm_alg hm_ne
  have hLc := lamC_ne_zero' S.lam hc_alg hc_ne
  have hma := fun (e : ℤ) => zpow_mem hm_alg e
  have hca := fun (e : ℤ) => zpow_mem hc_alg e
  rw [lamC_mul' S.lam hm_alg (hca _), lamC_zpow' S.lam hc_alg] at ha
  rw [lamC_mul' S.lam (inv_mem hm_alg) (hca _), lamC_inv' S.lam hm_alg, lamC_zpow' S.lam hc_alg] at hb
  rw [hpp, hscal, lamC_mul' S.lam hsb (mul_mem (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _)),
    lamC_mul' S.lam (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _),
    lamC_mul' S.lam (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _),
    lamC_mul' S.lam (hma _) (inv_mem (hma _)), lamC_inv' S.lam (hma _),
    lamC_zpow' S.lam (hca _), lamC_zpow' S.lam (hca _), lamC_zpow' S.lam hm_alg, lamC_zpow' S.lam hm_alg,
    lamC_zpow' S.lam hc_alg, lamC_zpow' S.lam hc_alg,
    map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, ha, hb]
  have e1 : len (sysS H X std) v j Lb.2 = len (sysS H X std) v j La.2 + (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) := by ring
  have e2 : len (sysS H X std) v (j + 1) Lb'.2 = len (sysS H X std) v (j + 1) La'.2 +
      (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) := by ring
  generalize len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 = n at e1 ⊢
  generalize len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2 = n' at e2 ⊢
  rw [e1, e2]
  exact final hp0 hLm hLc _ _ _ _ _ _ _
end GlobalTheory.TwV.Xc.AwayId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact _root_.GlobalTheory.TwV.Xc.scal_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (_root_.GlobalTheory.pairOK_allSites S hd)

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  intro p _ X D pos Kc _ _ _ ι ρ hPT fd c hc j hN La' M hU hFr ν hν P hP
  obtain ⟨-, -, hsz', hle, -⟩ := _root_.GlobalTheory.TwV.DelA.size_first_last_rows X D pos j hN ν hν
  obtain ⟨R0, hR0⟩ := _root_.GlobalTheory.TwV.DelA.realises_of_wtPol X D pos j (rkT X D hN) (extNu (D.R.N (j + 1)) ν) hle P hP
  have hRR : phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P = R0 := _root_.GlobalTheory.TwV.DelA.phiC_eq_of_realises X D pos (j + 1) (rkT X D hN) _ P R0 hR0
  have hdeg := _root_.GlobalTheory.TwV.DelA.BlockHom.realises_blockHom X D pos (j + 1) (rkT X D hN) (wT X D pos j) (extNu _ ν) P R0 hP hR0
  have hphi : phi0 X D pos ι j P = MvPolynomial.map ι R0 := by
    unfold phi0
    rw [dite_eq_left (rkT X D hN)]
    show MvPolynomial.map ι (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P) = _
    rw [hRR]
  have hhom : ∀ m ∈ (MvPolynomial.map ι R0).support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 →
      (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) =
        (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = szT X D pos j τ := by
    intro m hm τ ho
    rw [hdeg m (MvPolynomial.support_map_subset _ _ hm) τ, if_neg ho, (_root_.GlobalTheory.TwV.DelA.eT_last_pair X D pos j τ).2, if_neg ho, ← hsz' τ]
    ring
  rw [hphi, hRR]
  unfold GlobalTheory.FrameB.tauV
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt X D pos Kc fd c j La' (fun τ => szT X D pos j τ) _ hhom,
    _root_.GlobalTheory.TwV.DelA.scal_tauV X D pos Kc ι ρ hPT fd c hc j hN La' M hU hFr ν hν, _root_.GlobalTheory.TwV.DelA.actC_inv_read X D pos Kc ι ρ hPT fd j hN La' M hU hFr R0, smul_smul, smul_smul]
  congr 1
  have hε : ∀ τ, ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ≠ 0 := fun τ =>
    (((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map ((ι.comp (embT D τ)))).ne_zero
  have hsum : c ^ (∑ τ, szT X D pos j τ) = ∏ τ, c ^ szT X D pos j τ := by
    classical
    induction (Finset.univ : Finset D.what₂.Tau) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hc, ih]
  rw [hsum, mul_assoc, ← map_mul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul, map_zpow₀, map_zpow₀]
  split_ifs with ho
  · rw [mul_one, ← zpow_add₀ (hε τ)]
    ring_nf
  · rw [one_mul, ← zpow_add₀ (hε τ)]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), cKs S ι j hj La.1 La'.1 * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) * ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hpos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hps := GlobalTheory.TwV.DelA.posTie_at S hpos ι hι
  intro d j hj La La'
  have hr := GlobalTheory.TwV.DelB.sysS_ranks S
  have hfr := _root_.GlobalTheory.TwV.DelA.changed_frame_unitary S d j (Nat.le_of_succ_le hj) (hr.2.2.1 j) La
  have hsc := _root_.GlobalTheory.TwV.DelA.source_scalar_const S d j hj ⟨La'.1⟩ La
  have hun := (_root_.GlobalTheory.TwV.DelA.cKs_unit_indep S hpos ι hι j hj La.1 La'.1).2.1
  have hcA := GlobalTheory.TwV.DelA.scal_inv_frame (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hps.1 d.fd2 j La (hr.2.2.1 j) (mM d j (Nat.le_of_succ_le hj) La) hfr.1 hfr.2.1
  have key : cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La * ι (d.uS S j La) =
      ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) := by
    rw [hcA, sO, dite_eq_left (Nat.le_of_succ_le hj), ← map_mul, ← map_mul, ← hsc]
    congr 1
    unfold dPow
    ring
  rw [mul_assoc (cKs S ι j hj La.1 La'.1), key]
  unfold cKs scT
  rw [dite_eq_left hj, map_mul ι (kT J j hj La'.1), map_inv₀, map_mul ι (d.uT S j La')]
  have hy : ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 := hun
  field_simp
end

