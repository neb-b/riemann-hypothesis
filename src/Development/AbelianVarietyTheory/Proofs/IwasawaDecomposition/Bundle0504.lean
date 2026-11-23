module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCuspIsThClsDOfPre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapsAgreeRootOfUnityEnlarged
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcIsEquivAtSerOfTie
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.PhaseOne

open GlobalTheory.PhaseRationalDegenerate GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples

theorem lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {x : ℝ}
    (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ GlobalTheory.PtId.degW Dw a := by
  have h : 0 < 2 * Real.pi * x := by positivity
  have e : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h, ← Real.exp_neg]
    congr 1
    ring
  rw [e, ← Real.exp_nat_mul, lieFac, GlobalTheory.PtId.degW]
  congr 1
  push_cast
  ring

theorem shape {c s l k m r : ℂ} (hc : c ≠ 0) : s * l * k * (m * r) = c * (c⁻¹ * s * k * l * m * r) := by
  field_simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rat

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

end Rat

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem wt_n (hT : TieIn T R κ v₀) (i : Fin D.R.m) : (κ i).n = (Vc D i).rank :=
  (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem fieldRange_le (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F := by
  rintro _ ⟨a, rfl⟩
  have h : ((O.jL a : O.c'.F) : ℂ) = D.what₂.embLL a := RingHom.congr_fun hP.lift.field a
  show D.what₂.embLL a ∈ O.c'.F
  exact h ▸ (O.jL a).2


set_option maxHeartbeats 1000000 in
theorem tieC_of_serOf (hR : PreChar R) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hs : SerOf O (κ i) (v₀ i (sg0 D A)) cc 1) :
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i))
      (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc 1 :=
  ⟨fieldRange_le O hP, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2,
    oneMapRow_of_serOf_ofPre D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP cc hs
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP)⟩

end GlobalTheory.RealGeo.PhaseOne

namespace GlobalTheory.RealGeo

open GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples PhaseOne


set_option maxHeartbeats 2000000 in
theorem exists_scalar_serOf {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (hC : PreChar R) (hT : TieIn T R κ v₀) (hio : IoExt R)
    (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃ s : ℂ, ‖s‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' →
      ∀ c0 : ℂ, ‖c0‖ = 1 → XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 →
      ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc → SerOf O (κ i) (v₀ i (sg0 D A)) ((c0⁻¹ * s) • cc) 1 := by
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨1, norm_one, fun Tp tup O hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := OneScalar.exists_scalar_ofPre D G Pl0 T0 A T R κ v₀ hC hT hio i c0L
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := ShortSeries.thetaKO_eq_short_series_ofPre D G Pl0 T0 A _ R hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ka * (((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) *
    (-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) := ⟨_, rfl⟩
  have hs1 : ‖s‖ = 1 := by
    rcases Int.units_eq_one_or δ with h | h <;> simp [hs, h, hka1]
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hcm : cmpConst D ka δ (GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) =
      s * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) := by
    rw [lieFac_eq_pow _ hx, hs, cmpConst]
    simp only [Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  refine ⟨s, hs1, fun Tp tup O hP hbc c0 h0 hxi cc hcc => ?_⟩
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (h0 ▸ one_ne_zero)
  refine ⟨fun k => ?_, norm_one, fun t h J' hR y x hx f _ hf g => ?_⟩
  · show ‖c0⁻¹ * s * cc k‖ = 1
    rw [norm_mul, norm_mul, norm_inv, h0, hs1, hcc.1 k]
    norm_num
  · have h2 := exact_identity_ofPre hC hT O hP (hka Tp tup O hP hbc) hδ
      (covAt_of_xiConst_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP c0 hxi) hcc t h J' hR y x hx f hf g
    rw [hcm] at h2
    refine mul_left_cancel₀ hne ((congrArg _ (one_mul _)).trans (h2.trans ?_))
    exact shape hne


set_option maxHeartbeats 1000000 in
theorem exists_serOf_of_ccIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP cc hcc
  obtain ⟨_, _, c0L, -, hbc⟩ := hP.lift.c0
  obtain ⟨c0, ⟨m, hm, hr⟩, hxi⟩ := hP.cxi
  have h0 : ‖c0‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hr hm.ne'
  obtain ⟨s, hs1, hs⟩ := exists_scalar_serOf hC hT hio i (c0L i)
  refine ⟨c0⁻¹ * s, ?_, hs Tp tup O hP hbc c0 h0 hxi cc hcc⟩
  rw [norm_mul, norm_inv, h0, hs1]
  norm_num


set_option maxHeartbeats 1000000 in
theorem exists_ccIs_equivAt_serOf_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i)) (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP
  obtain ⟨cc, hcc⟩ := CcEx.exists_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP
  obtain ⟨u, hu, hS⟩ := exists_serOf_of_ccIs D G Pl0 T0 A T R κ v₀ hC hT hio i Tp tup O hP cc hcc
  exact ⟨cc, hcc, u, hu,
    GlobalTheory.FrameConstMove.equivAt_of_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP cc hcc u, hS,
    tieC_of_serOf hC hT O hP hS⟩

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBase
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmCoef

theorem smul_eq_of_heq {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ a b : ℂ}
    (h1 : HEq x' (μ • y)) (h2 : HEq (a • x') (b • y)) : (a * μ) • y = b • y := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]
  exact eq_of_heq h2

theorem heq_smul {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ : ℂ}
    (h1 : HEq x' (μ • y)) (a : ℂ) : HEq (a • x') ((a * μ) • y) := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]

end GlobalTheory.Mem.R3.Rw.OmCoef


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hR i i' hii c0L hc
  obtain ⟨g'', c0R'', c0L'', hT''⟩ := hP.char.base.fam.tie
  have hc'' : GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' := ⟨g'', c0R'', hT''⟩
  by_cases h0 : ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
      (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0
  · exact Or.inl h0
  right
  push_neg at h0
  obtain ⟨x, hx⟩ := h0
  obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.Mem.R3.Rw.OmExt.coef_schur z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    _root_.GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc'' x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcv, -⟩ := hR
  obtain ⟨hW, -, hnW, hiW, -⟩ := hcv i i' hii
  have key := GlobalTheory.Mem.R3.Rw.OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i'),
    _root_.GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root R'.toRealDat c0L'' hc'' i' (u' * b⁻¹) (n * n') (mul_ne_zero hn hn') ha, fun v1 v1' h => ?_⟩
  have eu : Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i') i' =
      (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i' := Function.update_self _ _ _
  refine (heq_of_eq ((congrArg (fun g => g v1') eu).trans (LinearMap.smul_apply _ _ _))).trans ?_
  refine (GlobalTheory.Mem.R3.Rw.OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexArcOfAnalyticModelOnFlowOrbit
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.CuspFrom

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_similar_zeta
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a)) ∧
      ∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf, fun n hn => ?_⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rw [zpow_natCast]
    exact hν n hn

end

theorem familyUnif_lattice_similar_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty)
    (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧
      (∀ a, ∃ e, f l.A a = U.t i a + l.A • e) ∧
      σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) := by
  obtain ⟨-, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, -, -, h5, h6, h7⟩ := tateIso_similar_zeta
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h5, fun a ha => ?_, fun a => ?_, ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a
  · rw [← hζ, h7 _ l.A_pos]
    exact expNegUnit_zpow_val _ _

theorem exists_arcIn_input : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x B hσ _
  let _ := H.starRing
  intro A gam ξ DB tyB eB ex ⟨hgam, _, T₀, hT₀⟩ hrk hbe ⟨hχ, hψ⟩ ⟨hF, hty, _, hEF, _⟩ hp hq hp1 hq1
    ⟨_, hol, add, onto, ker, lin, weil⟩
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨T, m, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (RingHom.id ℂ)) B
  obtain ⟨-, hiso⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ _ B _ m
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ T.t.PP).1 T.t.sym
  have := T.t.act.hom H.w0
  obtain ⟨w, hw, hw'⟩ := CxFibre.exists_primGen T.t.PP (T.t.act.act H.w0) T.t.prim
  let oa : T.pol.OAct (𝓞 E) := ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hK.laws.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩
  obtain ⟨u, χ, hgP, lam, hAH, hrig, hθ, hex⟩ := CxFibre.exists_holUnif_of_exp hK.theta B.t.PP.isLB
    (spMap (RingHom.id ℂ)) T.pol T.t.PP.rig
    T.t.PP.rigGen m.φ m.cart ⟨w₀, hw₀⟩ A.abelian₂ A.discrete A.full A.Hm A.Hm_herm A.Hm_pos (fun a b => A.Ef a b) A.Ef_eq
    ex hol add onto
    (fun z => (ker z).trans ⟨fun ⟨a, ha⟩ => ha ▸ (eB a).2, fun hz => ⟨eB.symm ⟨z, hz⟩, by simp⟩⟩)
    (fun n a b c hn hc => by
      obtain ⟨a, rfl⟩ := eB.surjective a
      obtain ⟨b, rfl⟩ := eB.surjective b
      exact weil n a b c hn (by rw [hEF]; exact hc))
  have hact : ∀ (a : 𝓞 E) z, u.ex (fun i => tyB i (a : E) * z i) = u.ex z ≫ T.t.act.act a := fun a z =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by
      rw [hex, lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hex])
      (by rw [Over.w, Over.w]))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (A.F a z) = u.ex z ≫ T.t.act.act a := fun a z => by
    rw [← hact]; exact congrArg u.ex (funext (hF a z))
  obtain rfl : χ = fun b : u.Λ => A.chi ⟨b, lam.le b.2⟩ := funext fun a => by
    rw [CxFibre.chi_eq T.t.PP.isLB _ w hw u A.Hm χ hAH (A.F H.w0) (hact' _) a
      ⟨_, lam.ge (A.F_mem H.w0 a (lam.le a.2))⟩ rfl, hχ]
    have h₁ := A.Ef_eq_im (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩
    rw [← A.H_conj, Complex.conj_im] at h₁
    have h₂ : (hermForm A.Hm a (A.F H.w0 a)).im = -(A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ : ℤ) := by
      rw [h₁, neg_neg]; rfl
    generalize A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ = n at h₂
    rw [h₂, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  obtain ⟨s, hs, -⟩ := hT₀ ((T₀ + 1 : ℝ) * Complex.I) (by simp)
  obtain ⟨f, ν, f₁, f₂, f₃, f₄, f₅, f₆⟩ :=
    familyUnif_lattice_similar_zeta E H Dw l Xo _ _ _ Uw.F (Uw.ik k) _ (Uw.period k ⟨_, hs⟩)
  obtain ⟨a, Λ, hA, -, -, -, -, -, -, heta, hetaA⟩ := GlobalTheory.ArcOfModel.exists_arcIn hK.laws hK.laws2 Dw l
    (RingHom.id c.F) σ T.pol T.t.PP.rig T.t.PP.rigGen T.t.cub sym hsym hsym' oa ⟨w, hw, hw'⟩ A u lam hAH hrig
    (fun j _ => hθ j) hact' hψ (Module.nontrivial_of_finrank_pos (R := 𝓞 E) (hrk ▸ one_pos)) hbe _ gam hgam
    (Uw.F.t (Uw.ik k)) f ν f₁ (fun n hn v => ((f₂ n hn).1 v).1) (fun n hn => (f₂ n hn).2)
    f₃ f₄ f₅
    (fun z hz => (congrArg σ (Subtype.ext hz)).trans f₆)
    (fun ρ hρ τ => by
      obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
      have hρ' : σ ρ = H.rt0 := by
        rw [← hσ]
        exact congrArg σ (Subtype.ext hρ)
      refine ⟨_, CxFibre.lieMult_card hK.theta T.pol hgP u _ tyB hact τ₀, ?_⟩
      rw [hrk, hρ']
      split_ifs with h
      · rw [(hty τ₀).1 h]; omega
      · rw [(hty τ₀).2 h]; omega)
  refine ⟨a, Λ.toGtAn₀, hA, fun v q hq => ?_, fun v q hq => ?_⟩
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (heta v)]
    exact qk_equiv_refl a.bimult _
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (hetaA v)]
    exact qk_equiv_refl a.bimult _

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBaseLatticeEqSpanImages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftForms


set_option maxHeartbeats 4000000 in
theorem lift_Mj_base : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        (z'.R.FW j').Mj (z'.F.lv2.lvl false).P (z'.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.X).coeff g) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) {x' | ∃ x ∈ (z.R.FW j).Mj (z.F.lv2.lvl false).P (z.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.X).coeff g), ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro h1 h2 h3 h4 h5 h6 h7
  have hGoodForms := GlobalTheory.Mem.R3.Rw.goodForms_lift_bc h1 h2 h3 h4 h5 h6 h7
  have hSupLattice := GlobalTheory.Mem.R3.MKExt.mk_ext h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ hp => hp)
    (StepW.and hGoodForms hSupLattice)) (StepW.of_all ?_)
  rintro K B' f' T' w' - - ⟨-, H1, H2⟩ B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hW := H1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hK := H2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm e.nW j j' hj
  have key := span_rel_inf φ hn _ _ _ _ hK hW
  refine Eq.trans ?_ (key.trans ?_)
  · ext x
    simp only [Arith.FormsL.Mj, Arith.FormsL.Mall, RealDat.WL, Arith.FormsL.Wgood, Submodule.mem_inf,
      Submodule.restrictScalars_mem, and_assoc]
  · congr 1
    ext x'
    simp only [Set.mem_ofPred_eq, Arith.FormsL.Mj, Arith.FormsL.Mall, RealDat.WL, Arith.FormsL.Wgood, Submodule.mem_inf,
      Submodule.restrictScalars_mem, and_assoc]

end GlobalTheory.Mem.R3.LiftForms
end

