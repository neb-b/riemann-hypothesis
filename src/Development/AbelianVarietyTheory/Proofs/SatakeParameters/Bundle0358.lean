module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermImageSmooth
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory

theorem germImage_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  intro Z _ p hp inst hinst U hU h B hB
  exact smooth_sections_in_functionField Z p hp hinst U hU h B hB

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEvalComplexPointLeSpanJacobianStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  first | (exact @GlobalTheory.JacSpan.ker_le_span_jac) | (exact GlobalTheory.JacSpan.ker_le_span_jac) | (intros; apply GlobalTheory.JacSpan.ker_le_span_jac  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSource
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA


set_option maxHeartbeats 4000000 in
theorem moved_forms_at_source : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hjm hne hN
  have hj : j ≤ D.R.m := hjm.le
  have h : ((sysS H X std).Pj j).m + 1 = D.R.N j := rkS _ _ hN
  have hWt := _root_.GlobalTheory.TwV.DelA.wtOK_sites S j hjm hne
  have hPT := (posTie_at S hPos ι hι).1
  have hdg : ∀ τ, (t.O u μ).dgen τ ≠ 0 := by
    intro τ h0
    have h1 := _root_.GlobalTheory.TwV.DelB.dgen_unit S ι hι τ
    rw [h0, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hV : ∀ (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j),
      ((sysS H X std).Pj j).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat j).V, ∃ V : XR ((sysS H X std).Pj j) ℂ,
        MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp j x La.1 La.2) =
          MvPolynomial.map ι V ∧ RealAt d j hj h La ((ex.tw.fm u μ).emb j x) V := by
    intro j
    cases j with
    | zero => intro hj h La hL x; exact GlobalTheory.T.comparedForm_levelZero_realises_complexPoly S hDict hPos ι hι d h La hL x
    | succ k => intro hj h La hL x; exact GlobalTheory.T.comparedForm_normalisedValues_latticeTuple S hDict hPos ι hι d k hj h La hL x
  have core : ∀ La ∈ S.Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, K2.SharpQ t ex.tw u μ j x Q →
      GoodG (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x) ∧ OddDeg (sysS H X std) j (gmS d j La x) ∧
      ∀ n, AddMonoidAlgebra.coeff (polDel (sysS H X std) ℂ_[D.what₂.places.resChar w] j (gmS d j La x)) n =
        ι (sPt d j hj La * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) •
          AddMonoidAlgebra.coeff (trDY (sysS H X std) ℂ_[D.what₂.places.resChar w] j D (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)
            (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) (polDY D (t.O u μ).dgen (Q (clsAt X H j La.1 La.2)) (N' := D.R.N (j + 1)))) n := by
    intro La hLa x Q hQ
    have hL := S.Y.Rep_lat j La hLa
    obtain ⟨V, hVm, hVr⟩ := hV j hj h La hL x
    have hFr := _root_.GlobalTheory.TwV.DelA.changed_frame_unitary S d j hj h La
    have hmap := gmOf_map_eq_actC (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2 j La h
      (mM d j hj La) hFr.1 hFr.2.1 _ V hVm
    have hφ : ∀ y, (ex.tw.fm u μ).emb j x (clsAt X H j La.1 La.2) y =
        (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ)⁻¹ * frPoly (t.O u μ) j (Q (clsAt X H j La.1 La.2)) y := by
      intro y
      have h2 := congrFun (hQ.2 (clsAt X H j La.1 La.2)) y
      have hne : (∏ τ, (D.chTw u μ).de j y τ ^ (D.chTw u μ).sSharp j τ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne j y τ)
      rw [← h2]
      simp only [ColumnChain.sharp, mulFun, LinearMap.coe_mk, AddHom.coe_mk]
      field_simp
    have hR := (_root_.GlobalTheory.TwV.DelA.realAt_iff_realises S d j hj h La ((D.chTw u μ).sSharp j) ((ex.tw.fm u μ).emb j x) (Q (clsAt X H j La.1 La.2)) hφ V).1 hVr
    have hw : (fun τ => (D.chTw u μ).sSharp j τ - cTw D j) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.sh τ).symm
    rw [hw] at hR
    exact GlobalTheory.T.operatorPolynomial_of_realising_value (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι j hN (nuT D u j) hWt.nu
      (Q (clsAt X H j La.1 La.2)) (hQ.1 _) (sPt d j hj La) _ (gmS d j La x) hR hmap (t.O u μ).dgen hdg
  refine ⟨fun La hLa x => ?_, fun La hLa x Q hQ n => ?_, fun La hLa x Q hQ α hα => ?_⟩
  · obtain ⟨Q, hQ⟩ := J.sharp j hjm x
    obtain ⟨h1, h2, -⟩ := core La hLa x Q hQ
    exact ⟨_root_.GlobalTheory.TwV.DelA.natAct_glInv_gmOf (sysS H X std) D (hT.gat_pos u w hg) d.fd2 j La _, h1, h2⟩
  · rw [(core La hLa x Q hQ).2.2 n]
    simp only [sO, dif_pos hj]
  · exact polDY_goodDeg (sysS H X std) D (hT.gat_pos u w hg) j hN (nuT D u j) hWt.nu _ (hQ.1 _) _ α hα

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NullNegEvalOfJacobianDetEqZeroStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  first | (exact @GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (exact GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (intros; apply GlobalTheory.ChartSard.null_negEv_of_det_eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairwiseDisjointTriangularCells
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

theorem mem_span_X_of_pos {d n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (d + 1)) ℂ}
    (hf : f.IsHomogeneous n) : f ∈ Ideal.span (Set.range (X : Fin (d + 1) → MvPolynomial _ ℂ)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! H
  obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
  have := hf (mem_support_iff.1 hm)
  simp only [map_zero] at this
  omega

theorem iSup_chart_eq_top (d : ℕ) : ⨆ i, chart d i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _
    ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_pos hn hf)

theorem inf_chart_eq (d : ℕ) (I : Finset (Fin (d + 1))) :
    I.inf (fun i => chart d i) = Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (∏ i ∈ I, X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.prod_insert ha, Proj.basicOpen_mul, ih]

theorem preimage_chart_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ],
    (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧
      ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  intro d Z φ _
  constructor
  · rw [← Scheme.Hom.preimage_iSup, iSup_chart_eq_top, Scheme.Hom.preimage_top]
  · intro I hI
    have key : (I.inf fun i => φ ⁻¹ᵁ chart d i) = φ ⁻¹ᵁ (I.inf fun i => chart d i) := by
      classical
      clear hI
      induction I using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, ih, Scheme.Hom.preimage_inf]
    rw [key, inf_chart_eq]
    have hdeg : (∏ i ∈ I, X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ I.card := by
      have := SetLike.prod_mem_graded (homogeneousSubmodule (Fin (d + 1)) ℂ) (fun _ => 1) (fun i => X i)
        (F := I) (fun i _ => X_mem_one d i)
      simpa using this
    exact (Proj.isAffineOpen_basicOpen _ _ hdeg (Finset.card_pos.2 hI)).preimage φ

end GlobalTheory.PD.XCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
open MvPolynomial HomogeneousLocalization

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Overlap

variable {d : ℕ}

def awayRatio (i j : Fin (d + 1)) : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) :=
  Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j)

theorem ratioSec_eq (i j : Fin (d + 1)) :
    ratioSec d i j = Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) (awayRatio i j) := rfl

theorem germ_awayToSection_mul (a b : Fin (d + 1)) {x : MvPolynomial (Fin (d + 1)) ℂ} (hx : x = X a * X b)
    (y : PSpace ℂ d) (hya : y ∈ chart d a)
    (hy : y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) x)
    (s : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a)) :
    (PSpace ℂ d).presheaf.germ (chart d a) y hya
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) =
      (PSpace ℂ d).presheaf.germ _ y hy (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
        (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s)) := by
  have e := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ)
    (X_mem_one d b) hx) s
  simp only [ConcreteCategory.comp_apply] at e
  have e' : Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
      (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s) =
      (PSpace ℂ d).presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) := e
  rw [e', TopCat.Presheaf.germ_res_apply]

theorem awayRatio_mul_awayRatio (a i : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
        (rfl : X a * X i = X a * X i) (awayRatio a i) *
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i a) = 1 := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, Away.mk, Away.mk, val_awayMap_mk, val_awayMap_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem awayRatio_change (a i j : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i j) =
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
          (rfl : X a * X i = X a * X i) (awayRatio a j) *
        HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
          (mul_comm (X a) (X i)) (awayRatio i a) := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, awayRatio, Away.mk, Away.mk, Away.mk, val_awayMap_mk,
    val_awayMap_mk, val_awayMap_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem rat_eq_germ {Z : Scheme.{0}} [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (k l : Fin (d + 1))
    (hk : genericPoint Z ∈ φ ⁻¹ᵁ chart d k) :
    rat φ k l = φ.stalkMap (genericPoint Z) ((PSpace ℂ d).presheaf.germ (chart d k) _ hk (ratioSec d k l)) := by
  unfold rat
  rw [dite_eq_left hk]
  exact (Scheme.Hom.germ_stalkMap_apply φ _ _ hk _).symm

end Overlap


open Overlap in
theorem rat_overlap : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)),
    genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i →
      rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  intro d Z _ φ a i j ha hi
  have hW : φ (genericPoint Z) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) := by
    rw [Proj.basicOpen_mul]; exact ⟨ha, hi⟩
  let F := ((Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) ≫
    (PSpace ℂ d).presheaf.germ _ _ hW) ≫ φ.stalkMap (genericPoint Z)).hom
  have hA : ∀ l, rat φ a l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d i) (rfl : X a * X i = X a * X i) (awayRatio a l)) := by
    intro l
    rw [rat_eq_germ φ a l ha, ratioSec_eq, germ_awayToSection_mul a i rfl _ ha hW]
    rfl
  have hI : ∀ l, rat φ i l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d a) (mul_comm (X a) (X i)) (awayRatio i l)) := by
    intro l
    rw [rat_eq_germ φ i l hi, ratioSec_eq, germ_awayToSection_mul i a (mul_comm (X a) (X i)) _ hi hW]
    rfl
  have h1 : rat φ a i * rat φ i a = 1 := by
    rw [hA, hI, ← map_mul, awayRatio_mul_awayRatio, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
  rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h1, hI, hA, hI, ← map_mul, awayRatio_change]
end GlobalTheory.PD.XCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceFibreRingEqFinsumFibrePointsStatement
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (exact GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (intros; apply GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilIntegralParahoricEquivariance
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

noncomputable section

namespace GlobalTheory.PD.XCover

theorem finiteDimensional_of_finite {A B F K : Type} [CommRing A] [CommRing B] [Field F] [Field K] [Algebra F K]
    (ψ : B →+* A) (hψ : ψ.Finite) (g : A →+* K) (hB : ∀ b, g (ψ b) ∈ Set.range (algebraMap F K))
    (hfr : ∀ x : K, ∃ a b : A, g b ≠ 0 ∧ x * g b = g a) : FiniteDimensional F K := by
  letI := ψ.toAlgebra
  haveI : Module.Finite B A := hψ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := A)
  let M : Submodule F K := Submodule.span F (g '' (s : Set A))
  have hMfg : M.FG := Submodule.fg_span (s.finite_toSet.image g)
  have hM : ∀ a : A, g a ∈ M := by
    intro a
    have ha : a ∈ Submodule.span B (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul b x _ hx =>
      obtain ⟨c, hc⟩ := hB b
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]
      exact M.smul_mem c hx
  let R := Algebra.adjoin F (Set.range g)
  have hRM : Subalgebra.toSubmodule R ≤ M := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ g.range.toSubmonoid := (Submonoid.closure_le.2 (fun y hy => hy)) hx
    obtain ⟨a, rfl⟩ := hx'
    exact hM a
  have hRfg : (Subalgebra.toSubmodule R).FG := by
    haveI : FiniteDimensional F M := Module.Finite.iff_fg.2 hMfg
    exact isNoetherian_submodule.1 inferInstance _ hRM
  have htop : ∀ z : K, z ∈ M := by
    intro z
    obtain ⟨a, b, hb, e⟩ := hfr z
    have hbR : g b ∈ R := Algebra.subset_adjoin ⟨b, rfl⟩
    have hint : IsIntegral F (g b) := IsIntegral.of_mem_of_fg R hRfg _ hbR
    have hinv : (g b)⁻¹ ∈ R := Subalgebra.inv_mem_of_algebraic R (x := ⟨g b, hbR⟩) hint.isAlgebraic
    have hz : z = g a * (g b)⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [hz]
    exact hRM (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)
  have : M = ⊤ := eq_top_iff.2 fun z _ => htop z
  exact ⟨this ▸ hMfg⟩

variable {d : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ratioSec_eq (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  refine (GlobalTheory.ProjFrac.awayToSection_mk (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 _).trans ?_
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem exists_frac_germ (Z : Scheme.{0}) [IsIntegral Z] (U : Z.Opens) (hU : IsAffineOpen U) (h : genericPoint Z ∈ U)
    (x : Z.functionField) : ∃ a b : Γ(Z, U), (Z.presheaf.germ U _ h).hom b ≠ 0 ∧
      x * (Z.presheaf.germ U _ h).hom b = (Z.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, U)) x
  have hb' : algebraMap Γ(Z, U) Z.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem germ_app_mem (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) (φ : Z ⟶ PSpace ℂ d)
    (hp : φ ≫ PSpace.str ℂ d = p) (h : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (b : Γ(PSpace ℂ d, chart d 0)) :
    letI := ffAlg p
    (Z.presheaf.germ _ _ h).hom ((φ.app (chart d 0)).hom b) ∈ fld φ := by
  letI := ffAlg p
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d 0 b
  have e := congrArg (fun t => t P) (GlobalTheory.ProjSpace.appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ chart d 0) (i := 0) (hi := le_rfl))
  simp only [RingHom.comp_apply, RingHom.coe_coe] at e
  rw [← Scheme.Hom.appLE_eq_app, e, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine MvPolynomial.eval₂_mem (fun _ _ => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, hp]
    have hc : ∀ c : ℂ, (Z.presheaf.germ _ _ h).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom p (φ ⁻¹ᵁ chart d 0)).hom c) =
        algebraMap ℂ Z.functionField c := by
      intro c
      rw [← GlobalTheory.QCoh.Qcqs.baseRingHom_res p (le_top : φ ⁻¹ᵁ chart d 0 ≤ ⊤), Z.presheaf.germ_res_apply,
        GlobalTheory.QCoh.Qcqs.baseRingHom_top]
      rfl
    rw [hc]
    exact IntermediateField.algebraMap_mem _ _
  · have hr : (Z.presheaf.germ _ _ h).hom (GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl j) = rat φ 0 j := by
      rw [rat, dite_eq_left h, ratioSec_eq, ← Scheme.Hom.appLE_eq_app]
      rfl
    simp only [Function.comp_apply]
    rw [hr]
    exact IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩

theorem finiteDimensional_fld : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p →
    (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  intro d Z _ p _ inst hinst φ _ hp hgen
  subst hinst
  have hC : IsAffineOpen (chart d 0) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d 0
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d 0) := hC.preimage φ
  exact finiteDimensional_of_finite (φ.app (chart d 0)).hom (φ.finite_app _ hC) (Z.presheaf.germ _ _ (hgen 0)).hom
    (fun b => ⟨⟨_, germ_app_mem Z p φ hp (hgen 0) b⟩, rfl⟩) (exists_frac_germ Z _ hU (hgen 0))

end GlobalTheory.PD.XCover
end
end

