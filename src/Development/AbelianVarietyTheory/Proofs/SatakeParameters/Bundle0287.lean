module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLattice
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameLat

theorem locP_map_equiv' {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (e : W ≃ₗ[R] W') (q : Ideal R) [q.IsPrime] (Λ : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (e : W →ₗ[R] W')) = (Formalism.HermitianLatticesTheory.localization₂ q Λ).map (e : W →ₗ[R] W') := by
  ext x
  constructor
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have : s • e.symm x = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

theorem locP_mvL_comm {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ : Submodule (𝓞 E) (Fin N → E)) : Formalism.HermitianLatticesTheory.localization₂ q (mvL c Λ) = mvL c (Formalism.HermitianLatticesTheory.localization₂ q Λ) :=
  locP_map_equiv' ((toLE c).restrictScalars (𝓞 E)) q Λ

theorem mvL_one' {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : mvL 1 Λ = Λ := by
  unfold mvL
  convert Submodule.map_id _
  refine LinearMap.ext fun z => ?_
  show toLE 1 z = z
  rw [toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem span_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (h : Submodule.span E (Λ : Set (Fin N → E)) = ⊤) : Submodule.span E ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = ⊤ := by
  have e : ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = (toLE c : (Fin N → E) →ₗ[E] (Fin N → E)) '' (Λ : Set (Fin N → E)) := by
    unfold mvL
    rw [Submodule.map_coe]
    rfl
  rw [e, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (toLE c).surjective

end GlobalTheory.BaseFrameLat


open GlobalTheory.BaseFrameLat in
theorem GlobalTheory.TwV.baseFrame_std_eq_compan : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpins htie i hi β x p hp P
  have hd : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hR := _root_.GlobalTheory.FrameLat.seamGL_stdAt t.seam P.1 (frsF t.sel (t.tup μ) p P) p.deco.1.N (GlobalTheory.TopStep.frsF_mem p P)
  rw [hp.lat] at hR
  have hJ : IsUnit (gramN D i hi).det := by
    rw [← hpins.crd_orth i hi, Matrix.det_mul]
    have hc : IsUnit ((A.crd i hi).1).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.crd i hi).isUnit
    refine IsUnit.mul ?_ hc
    show IsUnit ((((A.crd i hi).1).map (sigD D : D.host.E →+* D.host.E))ᵀ).det
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hc.map _
  have hfg : (((St i hi).K β).lev.Lb).FG := Module.Finite.iff_fg.mp ((St i hi).K β).lev.Lb_fin
  have hsp := ((St i hi).K β).lev.Lb_span
  have h4 := GlobalTheory.T.companionLattice_adelicLattice_localization_eq D.sp (sigD D) rfl (gramN D i hi) hJ a x.1 x.2 _ hfg hsp (seamP t.seam P.1)
  have hCfg := GlobalTheory.T.companionHermitianLattice_fg D.sp (gramN D i hi) hJ a _ hfg hsp
  set C := compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb with hC
  have hCs : Submodule.span D.host.E (C : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    refine eq_top_iff.2 (hsp ▸ Submodule.span_mono ?_)
    intro z hz
    exact (le_sup_left : ((St i hi).K β).lev.Lb ≤ C) hz
  unfold latCo at hR
  rw [locP_mvL_comm, h4, ← locP_mvL_comm] at hR
  have e1 : mvL (A.crd i hi) (latAd x.1 C) = latAd (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (mvL (A.fb i hi β P)⁻¹ C) := by
    rw [_root_.GlobalTheory.TwV.latAd_mul_ratA, ← mvL_mul, mul_inv_cancel, mvL_one']
    exact (latAd_rat _ _ _).symm
  rw [e1] at hR
  have h3 := GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime (seamP t.seam P.1) _ hd _ _ (mvL (A.fb i hi β P)⁻¹ C) (hCfg.map _) (span_mvL _ _ hCs) (hp.frame P) hR.symm
  rw [← h3, ← locP_mvL_comm, ← mvL_mul, mul_inv_cancel, mvL_one']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.PhiTLev


set_option maxHeartbeats 2000000 in
theorem deco_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U) p p₁,
      x₁.1 = x.1 * κ.1 → IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ κ p p₁ hx hp hp₁
  have hL : latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb =
      latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab _ _ _ (hatStab_of_lev _ κ)]
  have hN : p₁.deco.1.N = p.deco.1.N := by
    have h := congrArg (latBack t.seam) ((hp₁.lat.trans hL).trans hp.lat.symm)
    rwa [latBack_seam_lat, latBack_seam_lat] at h
  refine ⟨hN, fun P => ?_⟩
  obtain ⟨v, hov, hTv, -⟩ := FnlAwayCpl.exists_place hTie P
  have hat : p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
    show Formalism.HermitianLatticesTheory.localization₂ _ p₁.deco.1.N = Formalism.HermitianLatticesTheory.localization₂ _ p.deco.1.N
    rw [hN]
  refine FnlAwayCpl.f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v (hTv j hj) _ _ _ κ (hp.fnl P v (hTv j hj) hov)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 = ratA D.host.F (A.crd j hj) * x.1 * κ.1 := by
    rw [hx, mul_assoc]
  rw [← e] at H
  have hu₁ : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb := by
    rw [← hp₁.lat]
    exact Submodule.subset_span ⟨w, hw₁, rfl⟩
  obtain ⟨z, hz⟩ := FnlAwayCpl.exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x₁.1 x₁.2
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb ((St j hj).K β).lev.Lb_fin
    ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu₁
  rw [hp₁.fnl P v (hTv j hj) hov w hw₁ z hz, H w hw z hz]


set_option maxHeartbeats 2000000 in
theorem phiT_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' z
  obtain ⟨hN, hf⟩ := deco_mul_lev A dtU a hPins hTie i (Nat.le_of_succ_le hi) β x x₁ κ p p₁ hx hp hp₁
  obtain ⟨hN', hf'⟩ := deco_mul_lev A dtU a hPins hTie (i + 1) hi β' x' x₁' κ' p' p₁' hx' hp' hp₁'
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun P => ?_
  simp only [Deco.at, hN, hN']
  refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
  rw [hf P y hy, hf' P (z y) hzy]

end GlobalTheory.TwV.PhiTLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeAtBadPlacesStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  first | exact @GlobalTheory.TwV.FnlAway.fnl_away | exact GlobalTheory.TwV.FnlAway.fnl_away | (intros; apply GlobalTheory.TwV.FnlAway.fnl_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  first | exact @GlobalTheory.TwV.fnl_eq_of_away_cpl | exact GlobalTheory.TwV.fnl_eq_of_away_cpl | (intros; apply GlobalTheory.TwV.fnl_eq_of_away_cpl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeUnderLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  first | exact @GlobalTheory.FnlAway.fnl_eq | exact GlobalTheory.FnlAway.fnl_eq | (intros; apply GlobalTheory.FnlAway.fnl_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.duty_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t hN hJ htw hS hE
  obtain ⟨t', hS', hR', -⟩ := _root_.GlobalTheory.Pdv.stdKer_stdRd I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  refine ⟨_root_.GlobalTheory.Pdv.colSide_of_std I hOk hP l Z L hT Gi Gl K Y cX ex t hN hS, hE, _root_.GlobalTheory.Pdv.rk_of_std I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS,
    ⟨t', _root_.GlobalTheory.Pdv.colSide_of_std I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS', ?_⟩⟩
  intro u μ _
  refine ⟨GlobalTheory.Pdv.stabStd I l Z u μ, ?_, _root_.GlobalTheory.Pdv.stab_pin I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS' hR' u μ⟩
  rw [htw]
  exact _root_.GlobalTheory.Pdv.FormsStd.formsAre_stabStd I hOk hP l Z l0 Y.Qp t'.O hS'.O u μ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTowerStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_characterSupportLift_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  first | (exact @GlobalTheory.RoadU.charLift_trans) | (exact GlobalTheory.RoadU.charLift_trans) | (intros; apply GlobalTheory.RoadU.charLift_trans  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTraceMatrixUnitsActsBySumInfinitesimalCh
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
noncomputable section

namespace GlobalTheory


open Polynomial in
theorem trace_Eop_of_hasInfChar (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ) (h : π.HasInfChar τ m) :
    ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hcard, hcap⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.card_eq_zero.1 hcard]; simp
  set c : ℂ := ((a : ℂ) - 1) / 2 with hc
  set P := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (GlobalTheory.CuspRep.Eop (a := a) τ) with hPdef
  have hP : P.coeff (a - 1) = ∑ i, GlobalTheory.CuspRep.Eop τ i i -
      algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) (((a : ℂ) * ((a : ℂ) - 1)) / 2) := by
    obtain ⟨-, -, hsub⟩ := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear a fun k =>
      GlobalTheory.CuspRep.Eop (a := a) τ k k - algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) ((k : ℕ) : ℂ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPdef, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.coeff_qdetPoly_top _ (a - 1) (by omega), hsub (a - 1) (by omega),
      Finset.sum_sub_distrib, ← map_sum, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.sum_fin_cast]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  let Q : ℂ[X] := ∑ j ∈ Finset.range (a + 1), C (ℓ (P.coeff j φ)) * X ^ j
  let R : ℂ[X] := C (ℓ φ) * (m.map fun z => X + C (z - c)).prod
  have hdeg : P.natDegree < a + 1 :=
    Nat.lt_succ_of_le (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_qdetPoly_le _)
  have hQ : ∀ v : ℂ, Q.eval v = ℓ ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU v P) φ) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum_range' _ hdeg, LinearMap.sum_apply, map_sum,
      eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, RingHom.id_apply, Module.End.mul_apply, ← map_pow,
      Module.algebraMap_end_apply, map_smul, map_smul, smul_eq_mul, mul_comm]
  have hQR : Q = R := by
    refine Polynomial.funext fun v => ?_
    rw [hQ, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly]
    have e := hcap (v - c) φ hφ
    rw [GlobalTheory.CuspRep.cap, show v - c + ((a : ℂ) - 1) / 2 = v by rw [hc]; ring] at e
    rw [e, map_smul, smul_eq_mul]
    simp only [R, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X]
    rw [mul_comm]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  have hco := congrArg (fun p : ℂ[X] => p.coeff (a - 1)) hQR
  have hlt : a - 1 ∈ Finset.range (a + 1) := Finset.mem_range.2 (by omega)
  simp only [Q, R, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hlt] at hco
  have hm : (m.map fun z => X + C (z - c)).prod =
      ((m.map fun z => z - c).map fun r => X + C r).prod := by rw [Multiset.map_map]; rfl
  rw [hm, Multiset.prod_X_add_C_coeff _ (by simp [hcard]), Multiset.card_map, hcard,
    show a - (a - 1) = 1 by omega, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map] at hco
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id', Multiset.sum_map_sub,
    Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at hco
  rw [hP] at hco
  simp only [LinearMap.sub_apply, map_sub, Module.algebraMap_end_apply, map_smul, smul_eq_mul] at hco ⊢
  rw [hc] at hco
  linear_combination hco

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Svd.Part.kerTie : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → O.ex.tw = w.tw Z ∧ O.ex.errX.piG = w.px.piG ∧ O.ex.errX.piT = w.px.piT ∧ TC.QpIs w.I O.X.Qp ∧ ∃ t : KerEntTied O.ex, TC.StdKer w.I w.l Z t ∧ t.Adapted ∧ t.TopPinned := by
  intro B f T w Z O P
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨pin, col, hErr, tp, hxi, qp, ker0, ker_eq, kt⟩ := P
  dsimp only [ofObj, extraObj] at hErr ker_eq qp kt
  cases ker_eq
  subst hErr
  have hpi := _root_.GlobalTheory.Svd.errXS_pi_of_colT B f T w Z col
  refine ⟨rfl, hpi.1, hpi.2, qp, ?_⟩
  refine Exists.imp (by intro t h; exact ⟨(StdModel.stdKer_iff w.I w.l Z t).2 h.1, h.2.2.2.1, h.2.2.2.2⟩)
    (GlobalTheory.Mem.Col2.TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z _ _ _ _ _ _ _ _ kt.O kt.E qp kt.std kt.unf kt.ok (by exact kt.served))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentsOfSmoothCharacters
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphUnr

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ms_eq_singleton {Δ : Segment k} (h1 : Δ.len = 1) : Δ.ms = {Δ.first} := by
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3]

open scoped Classical in
noncomputable def valAt (ϖ : kˣ) (y : IrrGL (k := k)) : ℂˣ :=
  if h : ∃ (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ), y = IrrGL.ofChar μ hμ then h.choose ϖ else 1

end Local

section Sph

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

end Sph

section Glob

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end Glob

end GlobalTheory.SphUnr

namespace GlobalTheory.SphUnr

end GlobalTheory.SphUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedMono

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem noMonodromy_of_mem_weilDeligneListSum : ∀ (l : List (WD h)), (sumList l).mono0 → ∀ y ∈ l, y.mono0
  | [], _, y, hy => by simp at hy
  | z :: l, H, y, hy => by
    have hsum := (WD.monomial_sum_iff z (sumList l)).mp H
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hsum.1
    · exact noMonodromy_of_mem_weilDeligneListSum l hsum.2 y hy

theorem lpTw_one_ne (x : WD h) (hx : 0 < x.lpDim) : x.lpTw 1 ≠ x := GlobalTheory.WeilDeligne.WD.lpTw_one_ne x hx

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

end

end GlobalTheory.UnlinkedMono
end
end

