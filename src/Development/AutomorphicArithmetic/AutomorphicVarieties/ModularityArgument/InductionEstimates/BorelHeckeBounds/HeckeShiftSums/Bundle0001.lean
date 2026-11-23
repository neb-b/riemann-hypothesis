module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Bundle0002
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusDifference

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.DiffBd
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate Pointwise Manifold ContDiff

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump {K : Type} [Field K] [NumberField K] {n : ℕ} {L : Set (ArchMatrix K n)}
    (hL : IsCompact L) (hLu : L ⊆ {x | IsUnit x}) :
    ∃ χ : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ L, χ x = 1) ∧
      tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  obtain ⟨M, hM, hLM, hMu⟩ := exists_compact_between hL Units.isOpen hLu
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := ⊤)
    𝓘(ℝ, ArchMatrix K n) hL.isClosed hLM
  have hsub : tsupport f ⊆ M :=
    closure_minimal (fun x hx => by_contra fun h => hx (h0 x h)) hM.isClosed
  refine ⟨f, f.contMDiff.contDiff, hM.of_isClosed_subset (isClosed_tsupport _) hsub,
    fun x hx => (h1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := hMu (hsub hx)
  exact ⟨u, rfl⟩

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {χ : ArchMatrix K n → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχu : tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) :
    (isExpLieAlgebra K n).IsTestFunction
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) := by
  refine ⟨((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_, ?_⟩
  · refine ContDiff.mul ?_ (((isExpLieAlgebra K n).isSmoothFun_iff).1 hf g)
    have e : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun Y : archLie K n =>
        (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n) := by
      have : (fun Y : archLie K n =>
          (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n)) =
          fun Y : archLie K n => ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (Y : ArchMatrix K n) := by
        funext Y
        simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
      rw [this]
      exact contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix K n)).comp (archLie K n).subtypeL.contDiff)
    exact Complex.ofRealCLM.contDiff.comp (hχ.comp e)
  · refine HasCompactSupport.intro
      ((isCompact_unitsSupport hχc hχu).image (archGroupEquiv K n).symm.continuous) fun a ha => ?_
    have : ((a : ArchUnits K n) : ArchMatrix K n) ∉ tsupport χ := fun h =>
      ha ⟨(a : ArchUnits K n), h, (archGroupEquiv K n).symm_apply_apply a⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {T : Set (archGroup K n)} (hT : IsCompact T) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
      ∀ A ∈ T, ‖∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩‖ ≤ c * ∏ i, ‖Y i‖ := by
  set T₀ : Set (ArchUnits K n) := (fun a : archGroup K n => (a : ArchUnits K n)) '' T with hT₀
  have hT₀c : IsCompact T₀ := hT.image continuous_subtype_val
  set T₁ : Set (ArchUnits K n) := (unipBall (K := K) (n := n) (k * R))⁻¹ * T₀ with hT₁
  have hT₁c : IsCompact T₁ := (isCompact_unipBall _).inv.mul hT₀c
  set L : Set (ArchMatrix K n) := (Units.val : ArchUnits K n → ArchMatrix K n) '' T₁ with hLdef
  have hLc : IsCompact L := hT₁c.image Units.continuous_val
  have hLu : L ⊆ {x | IsUnit x} := by
    rintro _ ⟨u, -, rfl⟩
    exact u.isUnit
  obtain ⟨χ, hχ, hχc, hχ1, hχu⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump hLc hLu
  have hκ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test hf hχ hχc hχu
  obtain ⟨B, hB⟩ := exists_norm_altSum_le (contDiff_matExt hκ) (hasCompactSupport_matExt hκ.2) k
  obtain ⟨Rt, hRt⟩ := hT₀c.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  refine ⟨max B 0 * max Rt 0 ^ k, mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _),
    fun Y hY hR C hC A hA => ?_⟩
  have hAT₀ : (A : ArchUnits K n) ∈ T₀ := ⟨A, hA, rfl⟩
  set v : Fin k → ArchMatrix K n := fun i => -(Y i * ((A : ArchUnits K n) : ArchMatrix K n)) with hv
  have hsum : ∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩ =
      altSum k (matExt K n fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) v
        ((A : ArchUnits K n) : ArchMatrix K n) := by
    rw [altSum_eq_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← val_inv_mul_eq hY (hC ε) (A : ArchUnits K n), zsmul_eq_mul]
    have hm := matExt_val (K := K) (n := n)
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a)
      ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩
    have hin : (((C ε)⁻¹ * (A : ArchUnits K n) : ArchUnits K n) : ArchMatrix K n) ∈ L :=
      ⟨_, ⟨(C ε)⁻¹, Set.inv_mem_inv.2 (mem_unipBall_of_val_eq hY hR (hC ε)), _, hAT₀, rfl⟩, rfl⟩
    simp only at hm
    rw [hm, hχ1 _ hin, Complex.ofReal_one, one_mul]
  rw [hsum]
  refine (hB v _).trans ?_
  have hA' : ‖((A : ArchUnits K n) : ArchMatrix K n)‖ ≤ max Rt 0 := (hRt _ hAT₀).trans (le_max_left _ _)
  have hprod : ∏ i, ‖v i‖ ≤ (∏ i, ‖Y i‖) * max Rt 0 ^ k := by
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [hv, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
  calc B * ∏ i, ‖v i‖ ≤ max B 0 * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ ≤ max B 0 * ((∏ i, ‖Y i‖) * max Rt 0 ^ k) := mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
    _ = max B 0 * max Rt 0 ^ k * ∏ i, ‖Y i‖ := by ring

private def UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n) (k : ℕ) (R : ℝ)
    (s : Set (G1 K n)) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
    ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
    ∀ w ∈ s, ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split {K : Type} [Field K] [NumberField K] {n : ℕ} {g : G1 K n}
    {u : AdelicGLn.integralFiniteGL K n} (hu : finPart K n (g : AdelicGLn.AdelicGL K n) = u) :
    g = finOne K n u * archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
  have hd : detA K n (infPart K n (g : AdelicGLn.AdelicGL K n)) = 1 :=
    detA_infPart (hu ▸ u.2)
  have hp : (archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) : AdelicGLn.AdelicGL K n) =
      infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
    rw [← retract_infEmb, coe_retractOne]
    have : detModule K n (infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n))) = 1 := hd
    rw [this, map_one, inv_one, mul_one]
  rw [← archimedeanProjection_mul_finiteEmbedding_comm]
  ext1
  rw [Subgroup.coe_mul, hp, coe_finOne, ← hu, infEmb_infPart_mul_finEmb_finPart]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n), IsLeftSmooth a → ∀ (k : ℕ) (R : ℝ), ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : G1 K n,
        ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖ := by
  intro K _ _ n a ha k R
  obtain ⟨hsm, U, hUo, hU⟩ := ha
  set Ω : Set (G1 K n) := (archProj K n '' unipBall (K := K) (n := n) (k * R)) * tsupport a with hΩdef
  have hΩ : IsCompact Ω :=
    ((isCompact_unipBall _).image continuous_archProj).mul a.hasCompactSupport
  have key : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn a k R Ω := by
    refine hΩ.induction_on ?_ ?_ ?_ ?_
    · exact ⟨0, le_rfl, fun _ _ _ _ _ w hw => absurd hw (Set.notMem_empty w)⟩
    · rintro s t hst ⟨c, hc, h⟩
      exact ⟨c, hc, fun Y hY hR C hC w hw => h Y hY hR C hC w (hst hw)⟩
    · rintro s t ⟨c, hc, h⟩ ⟨d, hd, h'⟩
      refine ⟨max c d, le_max_of_le_left hc, fun Y hY hR C hC w hw => ?_⟩
      have hp : 0 ≤ ∏ i, ‖Y i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      rcases hw with hw | hw
      · exact (h Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
      · exact (h' Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
    · intro x _
      have hcm : Continuous fun w : G1 K n => w * x⁻¹ := continuous_id.mul continuous_const
      set V : Set (G1 K n) := (fun w : G1 K n => w * x⁻¹) ⁻¹' finUSet U hUo with hV
      have hVc : IsClopen V := (isClopen_finUSet U hUo).preimage hcm
      have hxV : x ∈ V := by
        show x * x⁻¹ ∈ finUSet U hUo
        rw [mul_inv_cancel]
        show finPart K n ((1 : G1 K n) : AdelicGLn.AdelicGL K n) ∈ (finOpenSubgroup U hUo : Set _)
        rw [Subgroup.coe_one, map_one]
        exact one_mem (finOpenSubgroup U hUo)
      refine ⟨Ω ∩ V, inter_mem_nhdsWithin _ (hVc.isOpen.mem_nhds hxV), ?_⟩
      have hTc : IsCompact ((fun w : G1 K n => infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)) '' (Ω ∩ V)) :=
        (hΩ.inter_right hVc.isClosed).image
          (continuous_infPart.comp (continuous_subtype_val.comp hcm))
      obtain ⟨c, hc, h⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local (hsm x) hTc k R
      refine ⟨c, hc, fun Y hY hR C hC w hw => ?_⟩
      have hwV : finPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) ∈
          (finOpenSubgroup U hUo : Set (AdelicGLn.FiniteAdelicGL K n)) := hw.2
      rw [coe_openSubgroupOf] at hwV
      obtain ⟨u, huU, hu⟩ := hwV
      have hg := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split hu.symm
      obtain ⟨b, hbdef⟩ : ∃ b, b = infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := ⟨_, rfl⟩
      rw [← hbdef] at hg
      have hb := h Y hY hR C hC b ⟨w, hw, hbdef.symm⟩
      have hw' : w = finOne K n u * archP K n b * x := by
        rw [← hg, inv_mul_cancel_right]
      have hterm : ∀ ε, a ((archProj K n (C ε))⁻¹ * w) =
          a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
        intro ε
        have hpb : archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ =
            (archProj K n (C ε))⁻¹ * archP K n b := by
          rw [archimedeanProjection_apply, map_mul, map_inv, archimedeanProjection_apply]
        have e : (archProj K n (C ε))⁻¹ * w =
            finOne K n u * (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
          rw [hpb, hw', ← mul_assoc, ← mul_assoc, ← mul_assoc, archProj_inv_mul_finOne]
          simp only [mul_assoc]
        rw [e, hU u huU]
      have hs : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) =
          ∑ ε, (altSign ε : ℂ) * a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) :=
        Finset.sum_congr rfl fun ε _ => by rw [hterm ε]
      rw [hs]
      exact hb
  obtain ⟨c, hc, h⟩ := key
  refine ⟨c, fun Y hY hR C hC w => ?_⟩
  by_cases hw : w ∈ Ω
  · exact h Y hY hR C hC w hw
  · have hz : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) = 0 := by
      refine Finset.sum_eq_zero fun ε _ => ?_
      have : (archProj K n (C ε))⁻¹ * w ∉ tsupport a := fun hs =>
        hw ⟨archProj K n (C ε), ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), rfl⟩, _, hs, mul_inv_cancel_left _ _⟩
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    rw [hz, norm_zero]
    exact mul_nonneg hc (Finset.prod_nonneg fun i _ => norm_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem om_of_mul {K : Type} [Field K] [NumberField K] {T : ℝ} {γ : G1 K (2 + 2)} (hγ : γ ∈ Gam K (2 + 2))
    {x : G1 K (2 + 2)} (h : Om T x) : Om T (γ * x) := by
  intro q
  obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 (q.out * ⟨γ, hγ⟩)
  have h1 := h (Quotient.mk _ (q.out * ⟨γ, hγ⟩))
  unfold qx at h1 ⊢
  rw [e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ, Subgroup.coe_mul, mul_assoc] at h1
  exact h1

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omMeas :
    ∀ {K : Type} [Field K] [NumberField K] (T : ℝ), (∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x) ∧ IsClosed {x : G1 K (2 + 2) | Om T x} ∧
      MeasurableSet {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} := by
  intro K _ _ T
  have h1 : ∀ γ ∈ Gam K (2 + 2), ∀ x : G1 K (2 + 2), Om T (γ * x) ↔ Om T x := fun γ hγ x =>
    ⟨fun h => by
      have := om_of_mul (inv_mem hγ) h
      rwa [inv_mul_cancel_left] at this, om_of_mul hγ⟩
  have h2 : IsClosed {x : G1 K (2 + 2) | Om T x} := by
    unfold Om
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun q => isClosed_le
      ((hpSpec (K := K)).2.2.2.1.comp (continuous_const.mul continuous_id)) continuous_const
  refine ⟨h1, h2, ?_⟩
  rw [measurableSet_quotient]
  have h : Quotient.mk'' ⁻¹' {y : RightCosetSpace (Gam K (2 + 2)) | Om T (Quotient.out y : G1 K (2 + 2))} =
      {x : G1 K (2 + 2) | Om T x} := by
    ext x
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk (Gam K (2 + 2)) x))
    change Om T (Quotient.out (RightCosetSpace.mk (Gam K (2 + 2)) x)) ↔ Om T x
    rw [← hγ]
    exact h1 _ γ.2 x
  rw [h]
  exact h2.measurableSet
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GroundTheory.Automorphic.CuspidalProjection
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section

variable {K : Type} [Field K] [NumberField K]

private theorem unip_mem_iff {n r : ℕ} (Y : UPos n r → 𝔸[K]) :
    unipOne (K := _) (n := _) r Y ∈ Gam K n ↔ Y ∈ unipLattice K n r := by
  refine ⟨fun h => ?_, fun h => unipOne_mem_rationalGLOne r ⟨Y, h⟩⟩
  obtain ⟨g, hg⟩ : (unipGL Y : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.rationalGL K n := h
  refine ⟨fun p => (g : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2, funext fun p => ?_⟩
  have h1 := congrArg (fun x : AdelicGLn.AdelicGL K n => (x : Matrix (Fin n) (Fin n) 𝔸[K]) p.1.1 p.1.2) hg
  have hne : p.1.1 ≠ p.1.2 := fun e => by
    have := p.2
    rw [e] at this
    omega
  simp only [AdelicGLn.diagonal_apply, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2,
    Matrix.one_apply_ne hne, zero_add] at h1
  exact h1

private theorem ct_unip {n r : ℕ} {ψ : G1 K n → ℂ} (hψ : ∀ γ ∈ Gam K n, ∀ x, ψ (γ * x) = ψ x)
    (Y : UPos n r → 𝔸[K]) (z : G1 K n) : ct r ψ (unipOne (K := _) (n := _) r Y * z) = ct r ψ z := by
  unfold ct
  have h : ∀ X, unipOne (K := _) (n := _) r X * (unipOne (K := _) (n := _) r Y * z) = unipOne (K := _) (n := _) r (X + Y) * z := by
    intro X
    rw [unipOne_add, mul_assoc]
  simp_rw [h]
  refine setIntegral_add_right_of_periodic isAddFundamentalDomain_unipFundamentalDomain
    (h := fun X => ψ (unipOne (K := _) (n := _) r X * z)) (fun ξ hξ s => ?_) Y
  show ψ (unipOne (K := _) (n := _) r (ξ + s) * z) = ψ (unipOne (K := _) (n := _) r s * z)
  rw [unipOne_add, mul_assoc, hψ _ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]

private theorem ct_levi {ψ : G1 K (2 + 2) → ℂ} (hψ : ∀ γ ∈ Gam K (2 + 2), ∀ x, ψ (γ * x) = ψ x)
    (γ₁ γ₂ : G1 K 2) (hl : lv γ₁ γ₂ 0 ∈ Gam K (2 + 2)) (z : G1 K (2 + 2)) :
    ct 2 ψ (lv γ₁ γ₂ 0 * z) = ct 2 ψ z := by
  obtain ⟨e, he, -⟩ := adMeas γ₁ γ₂ 0
  have hlat : ∀ X, e X ∈ unipLattice K (2 + 2) 2 ↔ X ∈ unipLattice K (2 + 2) 2 := by
    intro X
    rw [← unip_mem_iff, ← unip_mem_iff]
    have h : unipOne (K := _) (n := _) 2 (e X) = (lv γ₁ γ₂ 0)⁻¹ * unipOne (K := _) (n := _) 2 X * lv γ₁ γ₂ 0 := by
      rw [mul_assoc, he X, inv_mul_cancel_left]
    rw [h]
    constructor
    · intro h'
      have h2 := mul_mem (mul_mem hl h') (inv_mem hl)
      simpa [mul_assoc] using h2
    · exact fun h' => mul_mem (mul_mem (inv_mem hl) h') hl
  have key := UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (2 + 2) 2 e hlat (fun X => ψ (unipOne (K := _) (n := _) 2 X * z)) (fun ξ hξ X => by
    show ψ (unipOne (K := _) (n := _) 2 (ξ + X) * z) = ψ (unipOne (K := _) (n := _) 2 X * z)
    rw [unipOne_add, mul_assoc, hψ _ (unipOne_mem_rationalGLOne 2 ⟨ξ, hξ⟩)])
  unfold ct
  rw [← key]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  show ψ (unipOne (K := _) (n := _) 2 X * (lv γ₁ γ₂ 0 * z)) = ψ (unipOne (K := _) (n := _) 2 (e X) * z)
  rw [← mul_assoc, he X, mul_assoc, hψ _ hl]

private theorem kc_ex {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) (r : ℕ) :
    ∃ kc : G1 K n → L2 μ, Continuous kc ∧ ∀ φ z, ⟪kc z, φ⟫_ℂ = ct r (rc μ a φ) z := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hk := kvCont K n μ a
  have hj : Continuous fun p : (UPos n r → 𝔸[K]) × G1 K n => kv μ a (unipOne (K := _) (n := _) r p.1 * p.2) :=
    hk.comp (continuous_unipOne_mul r)
  have hint : ∀ z, IntegrableOn (fun X => kv μ a (unipOne (K := _) (n := _) r X * z)) (unipFundamentalDomain K n r)
      (unipMeasure K n r) := fun z =>
    ((hj.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact hC).mono_set hDC
  haveI : IsFiniteMeasure ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
  refine ⟨fun z => ∫ X in unipFundamentalDomain K n r, kv μ a (unipOne (K := _) (n := _) r X * z) ∂unipMeasure K n r, ?_,
    fun φ z => ?_⟩
  · haveI : SecondCountableTopology (G1 K n) := inferInstance
    haveI : FirstCountableTopology (G1 K n) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds z₀
    obtain ⟨M, hM⟩ := (hC.prod hVc).exists_bound_of_continuousOn hj.continuousOn
    refine continuousAt_of_dominated (bound := fun _ => M)
      (Eventually.of_forall fun z => (hint z).aestronglyMeasurable) ?_ (integrable_const M) ?_
    · filter_upwards [hV] with z hz
      exact (ae_restrict_iff' measurableSet_unipFundamentalDomain).2
        (Eventually.of_forall fun X hX => hM (X, z) ⟨hDC hX, hz⟩)
    · exact Eventually.of_forall fun X => (hk.comp (continuous_const_mul _)).continuousAt
  · show ⟪∫ X in unipFundamentalDomain K n r, kv μ a (unipOne (K := _) (n := _) r X * z) ∂unipMeasure K n r, φ⟫_ℂ =
      ∫ X in unipFundamentalDomain K n r, rc μ a φ (unipOne (K := _) (n := _) r X * z) ∂unipMeasure K n r
    rw [← inner_conj_symm, ← integral_inner (hint z) φ, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    show conj ⟪φ, kv μ a (unipOne (K := _) (n := _) r X * z)⟫_ℂ = _
    rw [inner_conj_symm, inner_kv]

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctKv :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)), (∀ r, ∃ kc : G1 K (2 + 2) → L2 μ, Continuous kc ∧ ∀ φ z, ⟪kc z, φ⟫_ℂ = ct r (rc μ a φ) z) ∧
      ∀ φ : L2 μ, Continuous (rc μ a φ) ∧ Reps μ (Rop μ a φ) (rc μ a φ) ∧ (∀ γ ∈ Gam K (2 + 2), ∀ x, rc μ a φ (γ * x) = rc μ a φ x) ∧
        (∀ γ ∈ PK K, ∀ z, ct 2 (rc μ a φ) (γ * z) = ct 2 (rc μ a φ) z) ∧ ∀ X z, ct 2 (rc μ a φ) (nn X * z) = ct 2 (rc μ a φ) z := by
  intro K _ _ μ _ a
  refine ⟨fun r => kc_ex μ a r, fun φ => ?_⟩
  have hinv : ∀ γ ∈ Gam K (2 + 2), ∀ x, rc μ a φ (γ * x) = rc μ a φ x :=
    fun γ hγ x => rconv_mul_left (Gam K (2 + 2)) μ a φ hγ x
  refine ⟨continuous_rconv (Gam K (2 + 2)) μ a φ, ?_, hinv, fun γ hγ z => ?_, fun X z => ct_unip hinv X z⟩
  · have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ
    set_option synthInstance.maxHeartbeats 200000 in
    filter_upwards [QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ)
      (integrated_ae_eq_rconvQ (Gam K (2 + 2)) μ a φ)] with y hy
    exact hy
  · obtain ⟨ξ, γ₁, γ₂, rfl⟩ := (pkLaws (K := K)).2.1 γ |>.1 hγ
    have hγG : nn ξ.1 * lv (γ₁ : G1 K 2) (γ₂ : G1 K 2) 0 ∈ Gam K (2 + 2) := by
      obtain ⟨g, -, hg⟩ := hγ
      rw [← hg]
      exact g.2
    have hl : lv (γ₁ : G1 K 2) (γ₂ : G1 K 2) 0 ∈ Gam K (2 + 2) := by
      have h2 := mul_mem (inv_mem (unipOne_mem_rationalGLOne 2 ξ)) hγG
      simpa using h2
    rw [mul_assoc, ct_unip hinv, ct_levi hinv _ _ hl]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.VolOne
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.volOne :
    ∀ {K : Type} [Field K] [NumberField K] (n r : ℕ), unipMeasure K n r (unipFundamentalDomain K n r) = 1 ∧ volN K = 1 ∧
      ∃ C : Set (UPos n r → 𝔸[K]), IsCompact C ∧ unipFundamentalDomain K n r ⊆ C ∧ ∀ X : UPos n r → 𝔸[K], ∃ ξ : unipLattice K n r, ξ.1 + X ∈ C := by
  intro K _ _ n r
  have h1 : ∀ n r : ℕ, unipMeasure K n r (unipFundamentalDomain K n r) = 1 := fun n r => by
    rw [unipMeasure, unipFundamentalDomain, Measure.pi_pi]
    simp [GroundTheory.Global.adeleMeasure_fundamentalSet]
  refine ⟨h1 n r, ?_, ?_⟩
  · rw [volN, Measure.real, h1]; simp
  · obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
    refine ⟨C, hC, hsub, fun X => ?_⟩
    choose k hk _ using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
    refine ⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, hsub ?_⟩
    intro p _
    change algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hk p
end

