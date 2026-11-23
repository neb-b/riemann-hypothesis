module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominatorStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  first | exact @GlobalTheory.TwV.DelA.opId_denom | exact GlobalTheory.TwV.DelA.opId_denom | (intros; apply GlobalTheory.TwV.DelA.opId_denom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusGoodOfSelfDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist UpperTheory.V UpperTheory.V.Af ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem loc_eq_unrChar [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (hu : χ.UnrAt w) :
    χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
  refine MonoidHom.ext fun x => ?_
  have h2 := unif_spec w
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 := hu _ h1
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem satWD_map_mul (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (c : ℂˣ)
    {art : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h art)
    (hs : GlobalTheory.WeilDeligne.IsSmooth ((SmGL.unrChar (w.adicCompletion E) c).comp art)) :
    satWD h a (B.map (· * c)) = (satWD h a B).lpTwist _ hs := by
  have hM : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp art) hs =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := Test.lpOfChar_unrChar ha c hs
  have hMu : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).unr := (WD.unr_mk _).mpr (WDRep.unr_diag _)
  have hMf : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
    rw [WD.frobEig_diag]; simp
  have h0 : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  obtain ⟨hu0, hf0, -⟩ := WD.lpUnr_spec (h := h) _ h0
  have hU : WD.lpUnr (h := h) ((B.map (· * c)).map fun b => ((b⁻¹ : ℂˣ) : ℂ)) =
      (WD.lpUnr (h := h) (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpChar (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)) := by
    have hu1 := WD.unr_lpChar _ _ hu0 hMu
    rw [WD.unr_eq_lpUnr _ hu1, WD.frobEig_char _ _ _ hu0 hMu hMf, hf0, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [mul_inv_rev, mul_comm]
  rw [← lpChar_lpOfChar, hM, satWD, satWD, GlobalTheory.NuShift.lpChar_lpTw, hU]

end GlobalTheory.RoadU.PhiTwist


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonempty
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem joint_at_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  intro hC D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  obtain ⟨E, lam, hK⟩ := GlobalTheory.TwV.exists_cEmbC_lam t std J
  have hin := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨g, hLT, curve⟩ := hC D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) J.cop hin.1 hin.2.1 lam
  obtain ⟨Xi, muT, law⟩ := _root_.GlobalTheory.TwV.exists_adLawAt_joint t std J
  exact ⟨{ E := E, lam := lam, hK := hK, g := g, hLT := hLT, curve := curve, hfin := GlobalTheory.TwV.finClasses_sysS t std J, hst := GlobalTheory.TwV.finStab_site t std J, Xi := Xi, muT := muT, law := law }⟩

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtAllStd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000

theorem GlobalTheory.Svd.jointsAt_all_std : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → G.LatTied O.gatT O.Gx O.Gy → (∃ t : KerEntTied O.ex, ∀ μ, GlobalTheory.TwV.JointsAt t μ) ∧ ∀ u, O.ex.tw.e0 u (w.D Z).what₂.mu0 = O.ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B f T w Z O P hL
  obtain ⟨htw, -, hpiT, -, t, hstd, -, -⟩ := GlobalTheory.Svd.Part.kerTie B f T w Z O P
  have hchi := (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1
  obtain ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩ := O
  obtain ⟨pin, col, errX, tp, xi, qp, ker0, ker_eq, ker⟩ := P
  simp only [ofObj, extraObj] at ker_eq
  have h1 := congrArg Sigma.fst ker_eq
  simp only at h1
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj ker_eq).2
  have h3 := congrArg Sigma.fst h2
  simp only at h3
  obtain ⟨lev, th, th_io, cmp, lat, tw, exker⟩ := ex
  simp only at h3
  subst h3
  exact _root_.GlobalTheory.Pdv.oneTie_jointsAt_all w.I w.ok w.pins w.l w.l0 Z L col.Gt Gx Gy K X cX _ t col.C col.full col.g _ tp xi
    pin.isTw pin.jets htw hpiT hstd col.std col.stdLv col.stdDt col.herm_eq col.forms_eq hchi hL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem move_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact _root_.GlobalTheory.TwV.Xc.site_move S hD ⟨J.alg0, J.alg⟩ (pos_at_site S) (_root_.GlobalTheory.pairOK_allSites S hD)

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteScalarsAgreeAwayFromPlaceStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_scalars_agree_awayFromPlace : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∀ a b : (sysS H X std).G.Kf, S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) → S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))) → ∀ (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.pPow (sysS H X std) j La La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La') * S.E.iK (a ^ len (sysS H X std) v j Lb.2 * b ^ len (sysS H X std) v (j + 1) Lb'.2) = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb') * S.E.iK (a ^ len (sysS H X std) v j La.2 * b ^ len (sysS H X std) v (j + 1) La'.2)) := by
  first | exact @GlobalTheory.TwV.Xc.AwayId.scal_away | exact GlobalTheory.TwV.Xc.AwayId.scal_away | (intros; apply GlobalTheory.TwV.Xc.AwayId.scal_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFramePolynomialComplexValuesAtPoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem actC_actC_inv {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) :
    actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  let z : Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) := ⟨fun _ => 1, fun _ => by simp⟩
  let f : Fr1 D n := ⟨fun τ => (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ, fun τ => by
    show IsUnit ((atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * 1).det
    rw [mul_one]
    exact (Matrix.GeneralLinearGroup.det (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ)).isUnit⟩
  exact (evC_crdB_actC X D pos i h (fun _ => 1) 1 M V z f (fun _ => rfl)).2

theorem embT_det_ne_zero (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : embT D τ M.1.det ≠ 0 := by
  have h0 : M.1.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det M).ne_zero
    simpa using this
  exact (map_ne_zero _).2 h0

theorem transported_frame_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι
  intro d j hj h La' φ P hP hφ
  have hWt := _root_.GlobalTheory.TwV.DelA.wtOK_sites S j (by omega) ⟨La'.1⟩
  obtain ⟨-, -, -, hle, -⟩ := size_first_last_rows (sysS H X std) D (hT.gat_pos u w hg) j hWt.rk (nuT D u j) hWt.nu
  have hR : Realises (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P
      (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P) := by
    obtain ⟨R0, hR0⟩ := _root_.GlobalTheory.TwV.DelA.realises_of_wtPol (sysS H X std) D (hT.gat_pos u w hg) j h _ hle P hP
    exact selOf_mem (relPhi (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h _) P ⟨(P, R0), hR0, rfl⟩
  refine ⟨sPt d (j + 1) hj La' • actC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (mM d (j + 1) hj La')⁻¹
    (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P), ?_, ?_⟩
  · rw [_root_.GlobalTheory.TwV.DelA.realAt_iff_realises S d (j + 1) hj h La' (fun τ => (D.chTw u μ).sDiv j τ) φ P hφ, map_smul, actC_actC_inv]
    have hw : (fun τ => (D.chTw u μ).sDiv j τ - cTw D (j + 1)) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.dv τ).symm
    rw [hw]
    intro f
    have h1 := hR f
    simp only [GL3Theta.evFr, map_smul, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eval] at h1 ⊢
    rw [h1]
    ring
  · letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    have hPT := (posTie_at S hPos ι hι).1
    have hFr := _root_.GlobalTheory.TwV.DelA.changed_frame_unitary S d (j + 1) hj h La'
    have hτ := _root_.GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2
      (ltC S.g S.hLT) (ltC_ne_zero _ _) j hWt.rk La' (mM d (j + 1) hj La') hFr.1 hFr.2.1 (nuT D u j) hWt.nu P hP
    have h45 := _root_.GlobalTheory.TwV.DelA.target_scalar S d j hj La'
    have hprod : dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) *
        ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ = 1 := by
      unfold dPow
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (embT_det_ne_zero D _ τ))]
    have hc := ltC_ne_zero S.g S.hLT
    have key : ι (sPt d (j + 1) hj La') = scT d S ι j La'.1 La'.2 * (ltC S.g S.hLT ^ (∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ) *
        ι (∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) := by
      rw [scT, dite_eq_left hj]
      have e1 : sPt d (j + 1) hj La' = d.uT S j (La'.1, La'.2) * kT J j hj La'.1 *
          ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ := by
        rw [← h45, mul_comm (dPow _ _) (sPt _ _ _ _), mul_assoc, hprod, mul_one]
      rw [e1, map_mul, zpow_neg]
      field_simp
    rw [hτ, smul_smul, ← key, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalarStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), cKs S ι j hj La.1 La'.1 * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) * ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2) := by
  first | exact @GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT | exact GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT | (intros; apply GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT <;> assumption)
end

