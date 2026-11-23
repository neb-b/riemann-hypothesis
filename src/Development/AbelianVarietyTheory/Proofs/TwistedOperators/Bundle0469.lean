module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenAvgOne

open scoped ContDiff

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

def avg1 {K : Type} [MeasurableSpace K] (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure K)
    (j : K → GA D S) (c : K → ℂ) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, c k * om (j k, 1) Φ w ∂μ

theorem continuous_fam (hom : IsWeilDatumO ψ S T χS χT om) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {K : Type}
    [TopologicalSpace K] {p : K → GA D S × GA D T} (hp : Continuous p) :
    Continuous fun q : K × WO S T => om (p q.1) Φ q.2 :=
  (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp ((hp.comp continuous_fst).prodMk continuous_snd)

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {j : K → GA D S} {c : K → ℂ} {Φ : WO S T → ℂ}

theorem isThetaFunction_average_compactFamily_weilTranslates (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) : IsThetaFunO ψ S T (avg1 om μ j c Φ) := by
  have hψ := hom.std
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  refine ⟨fun γ w => ?_, ?_, ?_, ?_⟩
  · simp only [avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hom.om_pres _ _ hΦ).quasi]
    ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    simp only [heisO, avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    have := congrFun (hom.om_heis (j k) 1 u Φ hΦ) w
    rw [h u hu hu0, GlobalTheory.FrComb.actO_real (hj k) (GinfC T).one_mem hu0] at this
    rw [this, heisO]
    ring
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k w => c k * om (j k, 1) Φ w)
      ((hc.comp continuous_fst).mul (continuous_fam hom hΦ hp))
  · let gen : Set (K → WO S T → ℂ) := {F | ∃ (c : K → ℂ) (G : WO S T → ℂ), Continuous c ∧ IsThetaFunO ψ S T G ∧
      F = fun k => c k • om (j k, 1) G}
    have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO S T => F q.1 q.2 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact (hc.comp continuous_fst).mul (continuous_fam hom hG hp)
      | zero => exact continuous_const
      | add F F' _ _ h h' => exact h.add h'
      | smul a F _ h => exact h.const_smul a
    have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ S T (F k) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hom.om_pres _ _ hG)
      | zero => exact fun _ => GlobalTheory.WeilVacMove.isTheta_zero
      | add F F' _ _ h h' => exact fun k => GlobalTheory.WeilVacMove.isTheta_add (h k) (h' k)
      | smul a F _ h => exact fun k => GlobalTheory.WeilVacMove.isTheta_smul a (h k)
    have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
        (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ Submodule.span ℂ gen := by
      intro F hF M hM hM0
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.HeisLineComb.dLine_om_comb D ψ S T χS χT om hom M hM hM0
        have key : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (c k • om (j k, 1) G)) =
            ∑ i, fun k => (c k * e i (j k, 1)) • om (j k, 1) (GlobalTheory.WeilVacMove.dLine ψ S T (N i) G) := by
          funext k
          rw [GlobalTheory.CenAvg.dLine_smul, hexp _ _ hG, Finset.smul_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
        rw [key]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
          ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hG).2, rfl⟩
      | zero =>
        have : (fun k : K => GlobalTheory.WeilVacMove.dLine ψ S T M ((0 : K → WO S T → ℂ) k)) = 0 := by
          funext k x
          simp [GlobalTheory.WeilVacMove.dLine, heisO]
        rw [this]
        exact Submodule.zero_mem _
      | add F F' hF hF' h h' =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((F + F') k)) =
            (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) + fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F' k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
        rw [this]
        exact Submodule.add_mem _ h h'
      | smul a F _ h =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((a • F) k)) = a • fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_smul M a (F k)
        rw [this]
        exact Submodule.smul_mem _ a h
    intro n L hL hL0 w
    have := GlobalTheory.ThetaAvgSmooth.avg_smooth D ψ hψ S T K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _
      (Submodule.subset_span (show _ ∈ gen from ⟨c, Φ, hc, hΦ, rfl⟩)) n L hL hL0 w
    simpa only [avg1, Pi.smul_apply, smul_eq_mul] using this

theorem weilOperator_average_eq_average_translated [SecondCountableTopology K] [IsTopologicalGroup (GA D S)] [IsTopologicalGroup (GA D T)]
    (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) (p : GA D S × GA D T) (x : WO S T) :
    om p (avg1 om μ j c Φ) x = ∫ k, c k * om (p * (j k, 1)) Φ x ∂μ := by
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  have hm : ∀ k, om p (om (j k, 1) Φ) = om (p * (j k, 1)) Φ := fun k => by
    rw [map_mul, Module.End.mul_apply]
  have := GlobalTheory.CenAvg.om_integral μ hom hc (F := fun k => om (j k, 1) Φ) p (fun k => hom.om_pres _ _ hΦ)
    (continuous_fam hom hΦ hp) (by simp only [hm]; exact continuous_fam hom hΦ (continuous_const.mul hp))
    (isThetaFunction_average_compactFamily_weilTranslates μ hom hjc hj hc hΦ) x
  simp only [hm] at this
  exact this

end GlobalTheory.CenAvgOne

namespace GlobalTheory.CenAvgOne

theorem exists_central_average_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  intro D ψ S T χS χT om hom hsig hdef ν fd hν hfd χ φ hcen hφ Φ hΦ hint
  by_cases hz : φ = 0
  · subst hz
    exact ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun z _ _ => by simp, fun h => by simp⟩
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D S
  obtain ⟨j1, -, -, -, -, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D T
  let Z : Subgroup (GA D S) := GinfC S ⊓ Subgroup.center (GA D S)
  have hcl : IsClosed (Subgroup.center (GA D S) : Set (GA D S)) := by
    have : (Subgroup.center (GA D S) : Set (GA D S)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z :=
    isCompact_iff_compactSpace.mp ((Formalism.IndefR.Eqv.isCompact_GinfC hsig hdef).inter_right hcl)
  let m : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hz
  have hh : φ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hcen _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hcen _ b.2.1 b.2.2, hcen _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hcen _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ (h₀ * a) / φ h₀ := by
      funext a
      rw [hcen _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D S) ∈ GinfC S := fun a => a.2.1
  refine ⟨avg1 om m Subtype.val (fun a => χ a) Φ, isThetaFunction_average_compactFamily_weilTranslates m hom continuous_subtype_val hj hcont hΦ,
    fun a ha1 ha2 => ?_, fun h => ?_⟩
  · let a' : Z := ⟨a, ha1, ha2⟩
    have hne : χ a ≠ 0 := by
      intro h0
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel, OneMemClass.coe_one, hone] at this
      change 1 = χ (a'⁻¹ : Z) * χ a at this
      rw [h0, mul_zero] at this
      exact one_ne_zero this
    funext u
    rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ]
    simp only [Pi.smul_apply, smul_eq_mul, avg1]
    rw [← integral_mul_left_eq_self (μ := m) (fun b : Z => χ b * om ((b : GA D S), 1) Φ u) a', ← integral_const_mul]
    congr 1
    funext b
    rw [hmul a' b]
    change _ = (χ a)⁻¹ * (χ a * χ b * om ((a * b : GA D S), 1) Φ u)
    rw [Prod.mk_mul_mk, mul_one]
    field_simp
  · haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
    haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
    have hF_inv : ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h Φ * φ (γ * g) = thetaKO om g h Φ * φ g := by
      intro γ hγ g
      have : om (γ * g, h) Φ 0 = om (g, h) Φ 0 := by
        rw [show ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) by rw [Prod.mk_mul_mk, one_mul], map_mul,
          Module.End.mul_apply, hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ)]
      simp only [thetaKO, this, hφ.1 γ hγ g]
    have hF_cont : Continuous fun g => thetaKO om g h Φ * φ g :=
      ((hom.om_cont Φ hΦ 0).comp (continuous_id.prodMk continuous_const)).mul hφ.2
    have key : ∀ g, thetaKO om g h (avg1 om m Subtype.val (fun a => χ a) Φ) * φ g =
        ∫ k : Z, thetaKO om (g * k) h Φ * φ (g * k) ∂m := by
      intro g
      unfold thetaKO
      rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ, ← integral_mul_const]
      congr 1
      funext k
      rw [Prod.mk_mul_mk, mul_one, hcen _ k.2.1 k.2.2]
      ring
    simp_rw [key]
    exact (GlobalTheory.Chain.IoLift.AvgLift.setIntegral_average (GQ S) ν hfd m continuous_subtype_val
      (Φ := fun g => thetaKO om g h Φ * φ g) hF_inv hF_cont (hint h)).symm

end GlobalTheory.CenAvgOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingMemStabilizerAuxiliaryLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FinEmbLat

open Matrix
open scoped nonZeroDivisors TensorProduct

variable {D : D7}

theorem mulVec_mem_hatL_of_mapsTo {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E))
    (hN : ∀ x ∈ Λ, N *ᵥ x ∈ Λ') :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, N.map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have e : N.map (eToEAf D) *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) =
        fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((N *ᵥ x) i) := by
      funext i
      exact (RingHom.map_mulVec (eToEAf D) N x i).symm
    rw [e]
    exact Submodule.subset_span ⟨_, hN x hx, rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ha

variable {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem mapsTo_hatL_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (M : Matrix (Fin B.rank) (Fin B.rank) (Lev.EAf D)) (K : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D))
    (h1 : M * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * K)
    (h2 : M * d.a.map (eToEAf D) = d.a.map (eToEAf D))
    (hK : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, K *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1),
      M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) := by
  have hP : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      (frameMat B A d.ι).map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) :=
    mulVec_mem_hatL_of_mapsTo _ Λ _ fun x hx =>
      ⟨x, hx, 0, fun _ => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).zero_mem, by rw [mulVec_zero, add_zero]⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, ⟨y0, hy0, u, hu, rfl⟩, rfl⟩ := hv
    have e : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)
        (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) =
        (frameMat B A d.ι).map (eToEAf D) *ᵥ (fun i => eToEAf D (y0 i)) + d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) := by
      funext i
      rw [Pi.add_apply, Pi.add_apply, map_add (f := _)]
      exact congrArg₂ (· + ·) (RingHom.map_mulVec (eToEAf D) _ y0 i) (RingHom.map_mulVec (eToEAf D) d.a u i)
    show M *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)
        (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) ∈ _
    rw [e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, ← mulVec_mulVec]
    refine add_mem (hP _ (hK _ (Submodule.subset_span ⟨y0, hy0, rfl⟩))) ?_
    have e2 : d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) =
        fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((d.a *ᵥ u) i) := by
      funext i
      exact (RingHom.map_mulVec (eToEAf D) d.a u i).symm
    rw [e2]
    exact Submodule.subset_span ⟨_, ⟨0, zero_mem _, u, hu, by rw [mulVec_zero, zero_add]⟩, rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ha

end GlobalTheory.FinEmbLat

namespace GlobalTheory.FinEmbLat

open Matrix

theorem finEmb_mem_stabGL : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A), Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ) → Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) := by
  intro D A B c ε d Λ y hy
  have hrel := finEmb_rel d y
  set G' := Lev.finE B (finEmb d y).1 with hG'
  set Y := Lev.finE A y.1 with hY
  have h1 : G'.1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * Y.1 := by
    have := congrArg (fun X => X.map (toEAf D)) hrel.1
    simp only [Matrix.map_mul] at this
    exact this
  have h2 : G'.1 * d.a.map (eToEAf D) = d.a.map (eToEAf D) := by
    ext i p
    have hx := hrel.2 (fun k => d.a k p) (by
      funext k
      exact congrFun (congrFun d.perp k) p)
    have := congrArg (toEAf D) (congrFun hx i)
    rw [RingHom.map_mulVec] at this
    exact this
  have hK : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, Y.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    fun z hz => (hy z).1 hz
  have hKi : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Y⁻¹).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    fun z hz => ((Subgroup.inv_mem _ hy) z).1 hz
  have h1i : (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by
    calc (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D)
        = (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) * (Y.1 * (Y⁻¹).1) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (G'⁻¹).1 * ((frameMat B A d.ι).map (eToEAf D) * Y.1) * (Y⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = (G'⁻¹).1 * (G'.1 * (frameMat B A d.ι).map (eToEAf D)) * (Y⁻¹).1 := by rw [h1]
      _ = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have h2i : (G'⁻¹).1 * d.a.map (eToEAf D) = d.a.map (eToEAf D) := by
    conv_lhs => rw [← h2]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro v
  constructor
  · exact mapsTo_hatL_lat d Λ G'.1 Y.1 h1 h2 hK v
  · intro hv
    have := mapsTo_hatL_lat d Λ (G'⁻¹).1 (Y⁻¹).1 h1i h2i hKi _ hv
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end GlobalTheory.FinEmbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal

namespace GlobalTheory.CuspApproxAll

variable {D : D7}

def avgList (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  l.foldr (fun τ f => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) f) φ

theorem avgList_nil (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (φ : GA D N.V → ℂ) :
    avgList θ N e [] φ = φ := rfl

theorem avgList_cons (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (τ : D.what₂.Tau)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) :
    avgList θ N e (τ :: l) φ = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) (avgList θ N e l φ) := rfl

theorem growthSob_zero_ne_top {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (d : ℕ) :
    growthSob θ V d 0 φ ≠ ∞ := by
  let M : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | growthSize V 0 f ≠ ∞}
      add_mem' := fun a b => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a, b⟩) growthSize_add_le
      zero_mem' := (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top
      smul_mem' := fun c _ a => (growthSize_smul c).trans_ne (ENNReal.mul_ne_top enorm_ne_top a) }
  have hM : φ ∈ allDer θ V M := ⟨h.smooth, fun l hl => modGrowthExp_iff.1
    ((h.decay l hl).bounded.imp fun _ hC g => (hC g).trans_eq (by simp))⟩
  refine wordSum_ne_top_iff.2 fun l _ => ?_
  exact (wordAct_rel (A := glDer θ V) (B := glDer θ V) (R := fun f _ => f ∈ allDer θ V M) l
    (fun a _ _ _ hf => RderC_mem_allDer hf a.1 _) (y := φ) hM).2 [] (fun _ h => by simp at h)

def Good (θ : InfFam D) (V : HSp D) (f : GA D V → ℂ) : Prop := RapidDecSm θ V f ∧ IsCuspFun V f

theorem good_add {θ : InfFam D} {V : HSp D} {f f' : GA D V → ℂ} (h : Good θ V f) (h' : Good θ V f') :
    Good θ V (f + f') :=
  ⟨h.1.add h'.1, GlobalTheory.MultMem.isCuspFun_add h.1.toIsAutFun h'.1.toIsAutFun h.2 h'.2⟩

theorem good_smul {θ : InfFam D} {V : HSp D} {f : GA D V → ℂ} (c : ℂ) (h : Good θ V f) : Good θ V (c • f) :=
  ⟨h.1.smul c, GlobalTheory.MultMem.isCuspFun_smul c h.2⟩

theorem good_zero (θ : InfFam D) (V : HSp D) : Good θ V 0 := by
  refine ⟨rapidDecSm_iff.2 ⟨zero_mem _, ⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, ?_⟩
  exact fun _ _ _ _ _ _ _ _ => by simp

theorem good_value (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) (N : GlobalTheory.Grid.Node D) {Φ : N.Maps}
    (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) : Good θ N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, Good θ N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨rapidDecSm_of_cuspForm hP hθ (hx.aut w) (hx.cusp w), hx.cusp w⟩
    | zero => exact fun w => good_zero θ N.V
    | add x y _ _ hx hy => exact fun w => good_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => good_smul c (hx w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using good_smul r (hU' f)
  | add x y hx hy => simpa using good_add hx hy

end GlobalTheory.CuspApproxAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfLevelDatumNeZeroTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppLev

theorem supp_level : ∀ (D : D7) (S T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC T ΛT → IsFrame βT ΛT → T.rank ≤ S.rank → LT.Q = ∅ → IsIdemSum e Z → (∀ PP, PP ∈ Z ↔ PP ∈ LT.Pg ∨ PP ∈ Q) → ∀ g ∈ GfC T, ∀ x, levDatum S T βS βT LT Q m e x ≠ 0 → levDatum S T βS βT LT Q m e (actO S T 1 g x) ≠ 0 → ∃ k ∈ levG T βT LT, ∀ PP ∈ Z, projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g = projV T ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k := by
  classical
  intro D S T ΛT βS βT LT Q m Z e hsd hfr hrk hQ hZe hZ g hg x hx hx'
  have hu' := _root_.GlobalTheory.AdjAct.frMapAdj_actO S T βS βT g x
  obtain ⟨hh, hI, hU, a, ha1, ha2, ha3⟩ := _root_.GlobalTheory.FinZeta.levDatum_ne_zero_spec S T βS βT LT Q m e x hx
  obtain ⟨-, hI', hU', b, hb1, hb2, hb3⟩ := _root_.GlobalTheory.FinZeta.levDatum_ne_zero_spec S T βS βT LT Q m e _ hx'
  simp only [hu'] at hI' hU' hb1
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hZe
  have hsupp := _root_.GlobalTheory.HalfSupp.frMapAdj_supp S T βS βT e x hee hh
  obtain ⟨h1, h2, hred⟩ := _root_.GlobalTheory.HalfUnit.int_of_unit_tops S.rank T.rank hrk Z e hZe _ _ hI hI' hsupp
    (fun PP hP => hU PP ((hZ PP).1 hP)) (fun PP hP => hU' PP ((hZ PP).1 hP))
  have hUA := GlobalTheory.LevSplit.finE_mem_UA T g
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.ConjIntegral.conj_smul_isIntM T ΛT βT hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := _root_.GlobalTheory.IdemConjSum.idemSum_add_conj_idem Z e hZe
  obtain ⟨k, hk, hmt⟩ := _root_.GlobalTheory.GfCut.exists_cut T g (e + cA D e) hg hεε hεc
  refine ⟨k, ?_, fun PP hP => (_root_.GlobalTheory.CompIdem.projV_eq_of_idem T _ g k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt).symm⟩
  have hfk := _root_.GlobalTheory.FineCut.finE_cut T βT g k (e + cA D e) hmt
  obtain ⟨hSt, hR⟩ := _root_.GlobalTheory.FrameIdem.cut_mem_St_red T.rank βT _ _ Z e hZe h1 h2 h3 h4 hfk
  refine ⟨hk, ?_⟩
  refine _root_.GlobalTheory.MemLevRed.mem_lev_of_reductions T βT LT _ hQ (GlobalTheory.LevSplit.finE_mem_UA T k) hSt a b ha2 hb2 ha3 hb3 fun PP => ?_
  apply Units.ext
  rw [Units.val_mul, hR PP.1 ((hZ PP.1).2 (Or.inl PP.2)), ha1, hb1]
  exact hred PP.1 ((hZ PP.1).2 (Or.inl PP.2))

end GlobalTheory.SuppLev
end

