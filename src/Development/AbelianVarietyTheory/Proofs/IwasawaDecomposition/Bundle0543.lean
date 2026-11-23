module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0125
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaEqLam
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.Mem.LamPosTw

theorem adj_eig {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (θ : X →ₗ[ℂ] Y) (c : ℝ) (x₀ : X)
    (h : ∀ x', ⟪θ x₀, θ x'⟫_ℂ = (c : ℂ) * ⟪x₀, x'⟫_ℂ) : θ (LinearMap.adjoint θ (θ x₀)) = (c : ℂ) • θ x₀ := by
  have ha : LinearMap.adjoint θ (θ x₀) = (c : ℂ) • x₀ := by
    refine ext_inner_right ℂ fun x' => ?_
    rw [LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]
  rw [ha, map_smul]


set_option maxHeartbeats 2000000 in
theorem eig_parts : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ c, (∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.EEc c, R.HE.e x = U) ∧ (∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.Wc' i c, (R.HW i (sg0 D A3.A)).e x = U) := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨hC3, hSF, -, -, hEE, hWc, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hPins.char
  have hCore := hC3 hHolds.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  have hPY : GlobalTheory.StdFrame.StdPsi Y.hF Y.PY := Y.stdPsi.1
  have hPW : ∀ i, GlobalTheory.StdFrame.StdPsi Y.hF (Y.PW i) := Y.stdPsi.2
  obtain ⟨c, hc⟩ := GlobalTheory.Mem.R3.LabEig.exists_isSphScalars Y.hF (Y.PW ⟨0, Y.hm⟩) (hPW _) (principalLevelFrame.rowRepR R.θ (Y.eFT σ))
  refine ⟨c, fun b U hU => ?_, fun i U hU => ?_⟩
  · obtain ⟨x, hx, hxU⟩ := GlobalTheory.Mem.R3.LabEig.isotE_sub R.toRealDat F.lv2 hCore hS R.SF hSF Y.hF Y.PY Y.PW hPY hPW _ ⟨0, Y.hm⟩ c hc b U hU
    exact ⟨x, by rw [hEE]; exact hx, hxU⟩
  · obtain ⟨x, hx, hxU⟩ := GlobalTheory.Mem.R3.LabEig.isotL_sub R.toRealDat F.lv2 hCore R.SF hSF Y.hF Y.PW hPW _ ⟨0, Y.hm⟩ c hc i U hU
    exact ⟨x, by rw [hWc]; exact hx, hxU⟩


set_option maxHeartbeats 2000000 in
theorem carried : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  intro hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost c b x hx0 hxc hxb
  by_contra hno
  push_neg at hno
  obtain ⟨hcore, hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hP.char
  obtain ⟨h, -, hN, -, hev, hchar⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 (hcore hHo.aux.ex)
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCu R.toRealDat) R.SF hSF

  have heig : ∀ c' (y : R.HE.H), y ∈ R.EEc c' → ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P →
      GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) y = c' P (dualLab d) • y := by
    intro c' y hy P d hG hL
    rw [hEEc c'] at hy
    rw [hev c' P hG (Finsupp.single d 1) y hy]
    congr 1
    simp [GlobalTheory.Hk3.evC, Finsupp.sum_single_index, hL]

  have horth : ∀ c', R.EEc c' ≠ R.EEc c → R.EEc c' ≤ (ℂ ∙ x)ᗮ := by
    intro c' hne y hy
    have hex : ∃ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ GlobalTheory.Hk3.IsLab (Yc D 0) P d ∧
        c' P (dualLab d) ≠ c P (dualLab d) := by
      by_contra hall
      push_neg at hall
      apply hne
      ext z
      constructor
      · intro hz
        rw [hEEc c]
        exact hchar c z fun P d hG hL => by rw [heig c' z hz P d hG hL, hall P d hG hL]
      · intro hz
        rw [hEEc c']
        exact hchar c' z fun P d hG hL => by rw [heig c z hz P d hG hL, hall P d hG hL]
    obtain ⟨P, d, hG, hL, hcc⟩ := hex
    have hT : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) := by
      rw [hN.2 P hG]
      exact hN.1 P P hG hG _ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := GlobalTheory.Mem.R3.LabCarry.inner_eq_zero_of_normal _ hT hcc (heig c' y hy P d hG hL) (heig c x hxc P d hG hL)
    rw [← inner_conj_symm, this, map_zero]

  have hpart : ∀ p, R.EEp3 p ≤ (ℂ ∙ x)ᗮ := by
    intro p
    unfold RealDat3.EEp3
    refine iSup₂_le fun c' hc' => horth c' fun heq => hno p ?_
    exact GlobalTheory.Mem.R3.LabCarry.carries_of_eq R p heq hc'

  have hxT : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈ (R.toCx3 F).EEl b := hxb
  rw [← (hHo.prim.sumE b).2] at hxT
  have hxS : x ∈ ⨆ p, R.EEp3 p := by
    have h1 : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
      rw [GlobalTheory.Mem.R3.LabCarry.twSub_iSup]
      have hle : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤
          ⨆ p, Tw.sub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 p) := iSup_mono fun p => inf_le_left
      exact hle hxT
    exact h1
  have hself : x ∈ (ℂ ∙ x)ᗮ := (iSup_le hpart) hxS
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hself
  exact hx0 (inner_self_eq_zero.1 hself)


set_option maxHeartbeats 2000000 in
theorem hasLab_exists : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  intro hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨c, hE, hWp⟩ := eig_parts hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost σ
  have hcar := carried hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := hE b U hU
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxU
    exact hU0 hxU.symm
  obtain ⟨p, hp⟩ := hcar c b x hx0 hx (by rw [hxU]; exact hU.1)
  have hinjW : ∀ i, Function.Injective (R.HW i (sg0 D A3.A)).e := fun i => (hPins.char.base.models.HW i _).1
  refine ⟨p, fun i => ?_, fun k hk => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := (Y.tied.lift.isot i σ y).1 hy
    rw [Y.prtWE] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hWp i U' hU'
    rw [Y.mjRead] at hU'e
    have h2 : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) = (R.HW i (sg0 D A3.A)).e w := by
      rw [hwU]
      exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hU'e.symm
    have h3 : Y.mj.eW i y ∈ R.Wc' i c := (hinjW i h2) ▸ hw
    exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp le_rfl h3
  · have h1 := Y.tied.base.ft k
    rw [hk, Y.prtE0] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hE false U' hU'
    refine ⟨w, le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl hw, ?_⟩
    rw [← hU'e, hwU]
    rfl


set_option maxHeartbeats 2000000 in
theorem thetaMap_surjective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t _
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hb : Function.Bijective ((A3.indefDown (s0Of R F)).θ i t).mulVec :=
    CxData.liftMat_bij (R.toCx3 F) F.cr false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) hR.lifts0.1 hR.ratTh i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 :=
    ⟨hH.ok.ok2.conj, hH.ok.ok2.irr, hH.ok.ok2.lifts i t⟩
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj hB
  obtain ⟨hTh, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hTh.span i, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨z, hz⟩ := hb.2 (Pi.single k 1)
  refine ⟨D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z)), ?_⟩
  have hz' : lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) = z := by
    refine (Matrix.mulVec_mulVec _ _ _).trans ?_
    exact (congrArg (fun M => M *ᵥ z) hp.1).trans (Matrix.one_mulVec z)
  show _ = Z.jW i (Pi.single k 1)
  rw [hθ i t]
  exact congrArg (Z.jW i) ((congrArg (((A3.indefDown (s0Of R F)).θ i t).mulVec) hz').trans hz)


set_option maxHeartbeats 2000000 in
theorem inner_theta_eq_lam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  have hK := GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  set K := (LinearMap.ker θ)ᗮ with hKdef
  have hS := GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW

  have hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ := by
    intro z
    have := K.sub_starProjection_mem_orthogonal z
    rwa [Submodule.orthogonal_orthogonal] at this
  have hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ := fun z => K.sub_starProjection_mem_orthogonal z

  have hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K,
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), q⟫_ℂ := by
    intro a ha q hq
    rw [hK] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_right, inner_add_right, h1, h2, mul_add]
    | smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]; ring
  have hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x',
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ := by
    intro a ha x'
    have huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K := by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩
    have e1 : θ x' = θ (K.starProjection x') := by
      have := hkerK x'
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ := by
      have h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal huK (hKperp x')
      rw [inner_sub_right, sub_eq_zero] at h0; exact h0
    rw [e1, e2]
    exact hgoodK a ha _ (K.starProjection_apply_mem x')
  clear hx hW
  induction hS using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hgood a ha x'
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_left, inner_add_left, h1, h2, mul_add]
  | smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]; ring


set_option maxHeartbeats 2000000 in
theorem eigenvalue_eq_of_label : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne
  refine Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  obtain ⟨x, rfl⟩ := thetaMap_surjective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
  set K := (LinearMap.ker θ)ᗮ
  have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
    have := K.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at this
  have he : θ (K.starProjection x) = θ x := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
  have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
    rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
  have key := inner_theta_eq_lam D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
    (K.starProjection_apply_mem x) hW
  have := adj_eig θ (R.lam3 i t p A3.A.v0) _ key
  rw [he] at this
  exact this

end GlobalTheory.Mem.LamPosTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.AmpleFibres

theorem relAmple_restrict {S : Scheme.{0}} (U : S.Opens) [IsAffine U.toScheme] (B : Over S) {L : LB B.left}
    (hL : L.IsLB)
    (h : ReciprocityTheory.ChartRestriction.G.Out.RelAmple ((Over.pullback U.ι).obj B) (L.pull (pullback.fst B.hom U.ι))) :
    ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk (B.hom ∣_ U)) (L.pull (B.hom ⁻¹ᵁ U).ι) := by
  have hφ : (pullbackRestrictIsoRestrict B.hom U).inv ≫ pullback.fst B.hom U.ι = (B.hom ⁻¹ᵁ U).ι :=
    pullbackRestrictIsoRestrict_inv_fst B.hom U
  have hsq : IsPullback (pullbackRestrictIsoRestrict B.hom U).inv (Over.mk (B.hom ∣_ U)).hom
      ((Over.pullback U.ι).obj B).hom (𝟙 U.toScheme) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    simp [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hL₁ : (L.pull (pullback.fst B.hom U.ι)).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hL₂ : (L.pull (B.hom ⁻¹ᵁ U).ι).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hw : LBIso (L.pull (B.hom ⁻¹ᵁ U).ι)
      ((L.pull (pullback.fst B.hom U.ι)).pull (pullbackRestrictIsoRestrict B.hom U).inv) := by
    exact GenSpread.lbIso_pull_pull hL (pullbackRestrictIsoRestrict B.hom U).inv hφ.symm
  exact GlobalTheory.AmpleLocalBase.relAmple_baseChange hsq hL₁ hL₂ hw h

end GlobalTheory.AmpleFibres
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlatSec

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem tri_trans {R k : Type} [CommRing R] [Field k] {φ : c.F →+* R} {φ' φ'' : c.F →+* k} {x : Sp R ⟶ Z.X}
    {x' x'' : Sp k ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* k} {g : EigFrame Z φ' x'} {g' : EigFrame Z φ'' x''}
    {t d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (h : f.Tri ψ g t) (h' : g.Tri (RingHom.id k) g' d) :
    f.Tri ψ g' (fun τ i => t τ i * d τ i) := by
  have h1 : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id k)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨e1, e2, h'⟩ := h'
  rw [h1, Category.id_comp] at e1
  subst e1
  refine ⟨rfl, e2, fun τ i => ?_⟩
  choose a a1 a2 a3 using h τ
  obtain ⟨cf, b1, b2, b3⟩ := h' τ i
  simp only [h3, Category.id_comp] at b3
  let A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k := fun j i => a i j
  have hA : A.BlockTriangular id := fun j k hk => a2 k j hk
  obtain ⟨c1, c2⟩ := Guard.tri_mulVec hA b2
  refine ⟨A.mulVec cf, ?_, c1, tanLinG _ (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)) _ A cf _ a3 b3⟩
  rw [c2, b1, show A i i = t τ i from a1 i, Units.val_mul]

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

variable {K : Type} [Field K] (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ)

end Gen

end GlobalTheory.ShFam.FlatSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorFrHolo

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)

theorem isDerivAt0_of_cart {g : ℕ} {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) (pt : Sp ℂ ⟶ X') {e : (Fin g → ℂ) → (Sp ℂ ⟶ G')} (he : ∀ z, e z ≫ h' = pt)
    (hol : IsHolTo Set.univ fun z => e z ≫ φ) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ G'}
    (hv : v ≫ h' = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ pt) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  have H := (IsPullback.of_hasPullback h' pt).paste_horiz hc
  have key := FibreDeriv.isDerivAt0_of_isPullback H
    (e := fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp]))
    (fun z => pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hol)
    (v := pullback.lift v _ hv) (pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hd)
  simpa only [pullback.lift_fst] using isDerivAt0_comp_hom key (pullback.fst h' pt)

theorem isHolTo_lift {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) {n g : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (a : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (ha : IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => a bz.1 bz.2) (hp : IsHolTo B p)
    (w : ∀ b z, a b z ≫ h = p b ≫ f) :
    IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => hc.lift (a bz.1 bz.2) (p bz.1) (w _ _) := by
  let L : (Fin (n + g) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin g → ℂ) :=
    ((LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin g) ℂ ℂ)).toContinuousLinearEquiv
  have hC : IsOpen (L ⁻¹' (B ×ˢ Set.univ)) := (hB.prod isOpen_univ).preimage L.continuous
  have h1 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => a (L c).1 (L c).2 :=
    LocLift.isHolTo_comp ha hC L.differentiableOn fun _ h => h
  have h2 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => p (L c).1 :=
    LocLift.isHolTo_comp hp hC (β := fun c => (L c).1) (by fun_prop) fun _ h => h.1
  have h3 := holPair _ _ _ h f _ _ _ _ (fun c => w (L c).1 (L c).2) hC h1 h2
  have h4 := isHolTo_comp h3 hc.isoPullback.inv
  have key : ∀ c, pullback.lift (a (L c).1 (L c).2) (p (L c).1) (w _ _) ≫ hc.isoPullback.inv =
      hc.lift _ _ (w (L c).1 (L c).2) := fun c => hc.hom_ext
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.lift_fst]
      exact pullback.lift_fst _ _ _)
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_snd, IsPullback.lift_snd]
      exact pullback.lift_snd _ _ _)
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h4 ((hB.prod isOpen_univ)) (β := L.symm)
    L.symm.differentiableOn fun q hq => by simpa using hq) fun q _ => ?_
  refine Eq.trans ?_ (key (L.symm q)).symm
  simp only [L.apply_symm_apply]

section Family

open GlobalTheory.TrueCx.TorHolo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

end Family

end GlobalTheory.TrueCx.TorFrHolo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBOfChartPull
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.NefFibre

theorem isLB_of_chartPull {Y : Scheme.{0}} {A M : LB Y} (a : ChartPull A M (𝟙 Y)) (hM : M.IsLB)
    (hc : ∀ y : Y, ∃ i, y ∈ A.U i) : A.IsLB := by
  refine GlobalTheory.GenSpread.isLB_of_gm A hc ?_
  intro y i j k hi hj hk
  have hi' : y ∈ M.U (a.idx i) := a.le i hi
  have hj' : y ∈ M.U (a.idx j) := a.le j hj
  have hk' : y ∈ M.U (a.idx k) := a.le k hk
  rw [a.g y i j hi hj, a.g y j k hj hk, a.g y i k hi hk]
  exact gm_cocycle hM (𝟙 Y) y hi' hj' hk'

end GlobalTheory.NefFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section


open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in
theorem GlobalTheory.LineNorm.isTanBasis_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x e cf u) → GlobalTheory.LineNorm.IsTanBasis t x e := by
  intro E _ _ _ H X t R _ x g e he hb
  let v : Fin g → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun i => tanOf (he i)
  have hv : Full v := fun n => (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff v a n).1 (hb _ (isTan_tv n))
  refine ⟨he, fun S _ φ w hw => ?_⟩
  have h := full_bc φ hv (tanOf hw)
  exact (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff (fun i => resM φ (v i)) a (tanOf hw)).2 h
end
end

