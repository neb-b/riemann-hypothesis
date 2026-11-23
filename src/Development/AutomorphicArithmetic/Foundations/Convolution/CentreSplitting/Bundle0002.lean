module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0013
public import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
public import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import GroundTheory.AutomorphicForms.L2LocalComponents
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
public import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapHCMem
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.ConvolutionTheory.Dp.capHC_mem (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

theorem UpperTheory.ConvolutionTheory.Dp.capHC :
    UpperTheory.ConvolutionTheory.Dp.CapHC := by
  intro n u
  refine ⟨⟨_, capHC_mem n (u + ((n : ℂ) - 1) / 2)⟩, rfl, ?_⟩
  rw [HarishChandra.harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [HarishChandra.rhoVec, Pi.neg_apply]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CentralIntegrated
section
open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (π : BanachRep G E)

theorem kernel_uAction (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (f : h.smoothFuns (F := ℂ))
    (hf : h.IsTestFunction fun g => f.1 g⁻¹) :
    h.IsTestFunction (fun g => (h.rightUAction u f).1 g⁻¹) ∧ ∀ w : E,
      (h.uAction π u ⟨π.integrated μ (fun g => f.1 g⁻¹) w, h.isSmoothVector_integrated π μ hf w⟩ : E) =
        π.integrated μ (fun g => (h.rightUAction u f).1 g⁻¹) w := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap r =>
    have e : (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (algebraMap ℝ _ r)) f).1 g⁻¹) =
        fun g => (r : ℂ) * f.1 g⁻¹ := by
      rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply]
      rfl
    rw [e]
    refine ⟨IsExpLieAlgebra.IsTestFunction.const_mul hf (r : ℂ), fun w => ?_⟩
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, IsExpLieAlgebra.integrated_const_mul_kernel]
    exact (Complex.coe_smul r _).symm
  | ι x =>
    have e : (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x)) f).1 g⁻¹) =
        h.convDeriv (h.ofLie x) fun g => f.1 g⁻¹ := by
      show (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) f).1 g⁻¹) = _
      rw [IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
      funext g
      simp only [IsExpLieAlgebra.convDeriv, inv_inv]
    rw [e]
    refine ⟨IsExpLieAlgebra.IsTestFunction.convDeriv hf (h.ofLie x), fun w => ?_⟩
    show (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) ⟨_, h.isSmoothVector_integrated π μ hf w⟩ : E) = _
    rw [IsExpLieAlgebra.uAction_ι, IsExpLieAlgebra.coe_derivEnd, h.derivOp_integrated_convDeriv μ π hf]
  | mul a b ha hb =>
    obtain ⟨h1, h2⟩ := hb f hf
    obtain ⟨h3, h4⟩ := ha _ h1
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply]
    refine ⟨h3, fun w => ?_⟩
    rw [Module.End.mul_apply, ← h4 w]
    congr 2
    exact Subtype.ext (h2 w)
  | add a b ha hb =>
    obtain ⟨h1, h2⟩ := hb f hf
    obtain ⟨h3, h4⟩ := ha f hf
    rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply]
    refine ⟨IsExpLieAlgebra.IsTestFunction.add h3 h1, fun w => ?_⟩
    rw [LinearMap.add_apply, Submodule.coe_add, h2, h4]
    exact (h.integrated_add_kernel μ π h3 h1 w).symm

theorem central_map (hπ : ∀ g, ‖π g‖ ≤ 1) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range h.expG)) : ∀ {v : E} (hv : h.IsSmoothVector π v),
      (h.uAction π z ⟨π g v, h.isSmoothVector_map π hv _⟩ : E) = π g (h.uAction π z ⟨v, hv⟩) := by
  induction hg using Subgroup.closure_induction'' with
  | one => intro v hv; simp only [BanachRep.map_one_apply]
  | mem x hx => obtain ⟨X, rfl⟩ := hx; exact fun hv => h.uAction_map_expG π hπ hz hv X
  | inv_mem x hx => obtain ⟨X, rfl⟩ := hx; rw [← h.expG_neg]; exact fun hv => h.uAction_map_expG π hπ hz hv _
  | mul x y _ _ hx hy =>
    intro v hv
    simp only [BanachRep.map_mul_apply]
    rw [hx (h.isSmoothVector_map π hv y), hy hv]

theorem central_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) (hG : Subgroup.closure (Set.range h.expG) = ⊤)
    {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU) {f : G → ℂ} (hf : h.IsTestFunction f) {w : E}
    (hw : h.IsSmoothVector π w) :
    (h.uAction π z ⟨π.integrated μ f w, h.isSmoothVector_integrated π μ hf w⟩ : E) = π.integrated μ f (h.uAction π z ⟨w, hw⟩) := by
  have hListContinuous (D : List 𝔤) : Continuous fun g : G => h.listOp π D (π g w) := by
    simpa only [h.listOp_eq_wordOp π] using
      h.continuous_wordOp_map π hπ hw (fun i : Fin D.length => D[i])
  have hListIntegral (D : List 𝔤) :
      h.listOp π D (π.integrated μ f w) = ∫ g, f g • h.listOp π D (π g w) ∂μ := by
    induction D with
    | nil => rfl
    | cons X D ih =>
      have hSmooth : h.IsSmoothVector π (∫ g, f g • h.listOp π D (π g w) ∂μ) := by
        rw [← ih]
        exact h.isSmoothVector_listOp π (h.isSmoothVector_integrated π μ hf w) D
      rw [h.listOp_cons, ih]
      simpa only [h.listOp_cons] using
        h.derivOp_integral π μ hπ hf (hListContinuous D)
          (fun g => h.isSmoothVector_listOp π (h.isSmoothVector_map π hw g) D) X
          (by simpa only [h.listOp_cons] using hListContinuous (X :: D)) hSmooth
  have hSumContinuous (L : List (ℂ × List 𝔤)) : Continuous fun g : G => h.wordSum π L (π g w) := by
    induction L with
    | nil => simpa only [h.wordSum_nil] using (continuous_const : Continuous fun _ : G => (0 : E))
    | cons p L ih =>
      simpa only [h.wordSum_cons] using ((hListContinuous p.2).fun_const_smul p.1).fun_add ih
  have hSumIntegral (L : List (ℂ × List 𝔤)) :
      h.wordSum π L (π.integrated μ f w) = ∫ g, f g • h.wordSum π L (π g w) ∂μ := by
    have := secondCountableTopology_subgroup_units G
    induction L with
    | nil => simp only [h.wordSum_nil, smul_zero, integral_zero]
    | cons p L ih =>
      have hHead : Integrable (fun g => f g • h.listOp π p.2 (π g w)) μ :=
        ((hf.continuous h).smul (hListContinuous p.2)).integrable_of_hasCompactSupport hf.2.smul_right
      have hTail : Integrable (fun g => f g • h.wordSum π L (π g w)) μ :=
        ((hf.continuous h).smul (hSumContinuous L)).integrable_of_hasCompactSupport hf.2.smul_right
      rw [h.wordSum_cons, ih, hListIntegral p.2, ← integral_smul, ← integral_add (hHead.fun_smul p.1) hTail]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [h.wordSum_cons, smul_add, smul_comm p.1 (f g)]
  obtain ⟨L, hL⟩ := h.exists_wordSum π z
  refine (hL ⟨_, h.isSmoothVector_integrated π μ hf w⟩).trans ((hSumIntegral L).trans ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (f g • ·) ((hL ⟨π g w, h.isSmoothVector_map π hw _⟩).symm.trans
    (central_map h π hπ hz (hG ▸ Subgroup.mem_top g) hw))

end General

end UpperTheory.ConvolutionTheory.Dp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClosureSummand
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Dp.closureSummand :
    UpperTheory.ConvolutionTheory.Dp.ClosureSummand := by
  intro K _ _ n μ _ U hU hs h0 hirr
  have hcl : IsClosed (cuspidalL2 μ : Set (LL μ)) := (completeSpace_coe_iff_isComplete.1 (inferInstanceAs (CompleteSpace (CuspL2 μ)))).isClosed
  have hle : (U.map (clsL μ)).topologicalClosure ≤ cuspidalL2 μ :=
    Submodule.topologicalClosure_minimal _ (by rintro _ ⟨φ, -, rfl⟩; exact toLp_mem μ _) hcl
  have hI := isInvariant_topologicalClosure_map μ hU hs.ρ hs.σ hs.τ
  have hmap : ∀ y ∈ (U.map (cuspVecL μ)).topologicalClosure, toLp μ y ∈ (U.map (clsL μ)).topologicalClosure := fun y hy =>
    Submodule.topologicalClosure_minimal (U.map (cuspVecL μ))
      (t := (U.map (clsL μ)).topologicalClosure.comap (toLp μ).toLinearMap)
      (by rintro _ ⟨φ, hφ, rfl⟩; exact Submodule.le_topologicalClosure (U.map (clsL μ)) ⟨φ, hφ, rfl⟩)
      ((Submodule.isClosed_topologicalClosure _).preimage (toLp μ).continuous) hy
  refine ⟨hle, Submodule.isClosed_topologicalClosure _, fun g v hv => ?_, fun e => h0 ?_, fun V' hV' hc hi => ?_⟩
  · refine mem_of_mem_topologicalClosure (Submodule.isClosed_topologicalClosure _) (rightRegularRep (rationalGLOne (K := K) (n := n)) μ g) ?_ hv
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmap _ (hI g _ (Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩))
  · refine eq_bot_iff.2 fun φ hφ => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hU hφ) (toLp_injective μ ?_)
    have h1 : clsL μ φ ∈ (U.map (clsL μ)).topologicalClosure := Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩
    rw [e, Submodule.mem_bot] at h1
    exact h1.trans (map_zero (toLp μ)).symm
  · refine or_iff_not_imp_left.2 fun hne => le_antisymm hV' ?_
    set W := V'.comap (toLp μ).toLinearMap with hW
    have hWc : IsClosed (W : Set (CuspL2 μ)) := hc.preimage (toLp μ).continuous
    have hWi : (cuspRepT μ).IsInvariant W := fun g v hv => hi g _ hv
    have hW0 : W ≠ ⊥ := by
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact (Submodule.ne_bot_iff _).2 ⟨(⟨v, hle (hV' hv)⟩ : cuspidalL2 μ), hv, fun e => hv0 (congrArg Subtype.val e)⟩
    obtain ⟨φ, hφ, hφ0, hφW⟩ := exists_cuspForm_mem_of_ne_bot μ hWc hWi hW0
    have h1 : summandCuspForms W ≤ U := fun ψ hψ => by
      rw [← formsClosure K n μ U hU hs]
      exact ⟨hψ.1, hV' hψ.2⟩
    rcases hirr _ h1 ⟨summandCuspForms_stable_ρ hWc hWi, summandCuspForms_stable_σ hWi, summandCuspForms_stable_τ hWi⟩ with e | e
    · have h2 : φ ∈ summandCuspForms W := mem_summandCuspForms.2 ⟨hφ, hφW⟩
      rw [e, Submodule.mem_bot] at h2
      exact (hφ0 h2).elim
    · have hmin : U.map (clsL μ) ≤ V' := by
        rintro _ ⟨ψ, hψ, rfl⟩
        have h3 : ψ ∈ summandCuspForms W := e.ge hψ
        exact (mem_summandCuspForms.1 h3).2
      exact fun v hv => closure_minimal (show ((U.map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆ V' from hmin) hc hv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DiracSep
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open scoped InnerProductSpace Topology

private theorem near_one_nhds {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) {v : H} (hpos : 0 < ‖v‖) :
    {g : G | ‖π g v - v‖ < ‖v‖ / 2} ∈ 𝓝 (1 : G) := by
  have hcont : Continuous fun g => π g v := π.continuous_orbit v
  have ht : Filter.Tendsto (fun g => ‖π g v - v‖) (𝓝 (1 : G)) (𝓝 ‖π 1 v - v‖) :=
    (hcont.sub continuous_const).norm.tendsto 1
  rw [UnitaryRep.map_one_apply, sub_self, norm_zero] at ht
  exact ht.eventually_lt_const (half_pos hpos)

private theorem exists_bump_nonzero {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) {v : H} (hpos : 0 < ‖v‖) (ρ : G → ℝ) (β : CompactlySupportedContinuousMap G ℂ)
    (hβa : ∀ g, β g = (ρ g : ℂ)) (hρ0 : ∀ g, 0 ≤ ρ g) (hρ1 : ∫ g, ρ g ∂ν = 1)
    (hρN : ∀ g, ρ g ≠ 0 → g ∈ {g : G | ‖π g v - v‖ < ‖v‖ / 2})
    (h2 : π.integrated ν (UnitaryRep.ccToL1 ν β) v = 0) : False := by
  have hcont : Continuous fun g => π g v := π.continuous_orbit v
  have hin : ∫ g, (ρ g : ℂ) * ⟪v, π g v⟫_ℂ ∂ν = 0 := by
    have h1 := CuspidalProjection.inner_integrated_ccToL1 ν π β v v
    rw [h2, inner_zero_right] at h1
    simp only [hβa] at h1
    exact h1.symm
  have hρi : Integrable ρ ν := by
    by_contra h
    rw [integral_undef h] at hρ1
    exact zero_ne_one hρ1
  have hint : ∀ F : G → ℂ, Continuous F → Integrable (fun g => (ρ g : ℂ) * F g) ν := fun F hF => by
    simp only [← hβa]
    exact (β.continuous.mul hF).integrable_of_hasCompactSupport (β.hasCompactSupport.mul_right)
  have hc1 : Continuous fun g => ⟪v, π g v⟫_ℂ := continuous_const.inner hcont
  have e : ∫ g, (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ ∂ν = -⟪v, v⟫_ℂ := by
    have h3 : (fun g => (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ) =
        fun g => (ρ g : ℂ) * ⟪v, π g v⟫_ℂ - (ρ g : ℂ) * ⟪v, v⟫_ℂ := by
      funext g
      rw [inner_sub_right, mul_sub]
    rw [h3, integral_sub (hint _ hc1) (hint _ continuous_const), hin, integral_mul_const,
      integral_complex_ofReal, hρ1]
    simp
  have hb : ‖∫ g, (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ ∂ν‖ ≤ ∫ g, ρ g * (‖v‖ * (‖v‖ / 2)) ∂ν := by
    refine norm_integral_le_of_norm_le (hρi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rcases eq_or_ne (ρ g) 0 with h0 | h0
    · simp [h0]
    · have hg : ‖π g v - v‖ < ‖v‖ / 2 := hρN g h0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 g)]
      refine mul_le_mul_of_nonneg_left ?_ (hρ0 g)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hg.le hpos.le)
  rw [e, integral_mul_const, hρ1, one_mul, norm_neg, inner_self_eq_norm_sq_to_K] at hb
  have h4 : ‖((‖v‖ : ℝ) : ℂ) ^ 2‖ = ‖v‖ ^ 2 := by simp
  have h5 : ‖v‖ ^ 2 ≤ ‖v‖ * (‖v‖ / 2) := by
    rw [← h4]
    simpa using hb
  nlinarith

theorem UpperTheory.ConvolutionTheory.Dp.diracSep :
    UpperTheory.ConvolutionTheory.Dp.DiracSep := by
  intro K _ _ n μ _ ν _ v hv
  by_contra hne
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hne
  obtain ⟨ρ, hρ0, hρt, hρ1, -, -, hρN, -⟩ := exists_archBump ν
    (near_one_nhds ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (archP K n) continuous_archP) hpos)
  let β : TI K n := ⟨⟨fun a => (ρ a : ℂ), hρt.continuous _⟩, hρt.2⟩
  exact exists_bump_nonzero ν _ hpos ρ β (fun _ => rfl) hρ0 hρ1 hρN (hv β hρt.1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.formsIrr :
    UpperTheory.ConvolutionTheory.Dp.FormsIrr := by
  intro K _ _ n μ _ V hV
  obtain ⟨hcs, hI, hirr⟩ := sumT K n μ V hV
  have hc : IsClosed ((V.comap (toLp μ).toLinearMap : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) :=
    hV.closed.preimage (toLp μ).continuous
  have e : formsIn μ V = summandCuspForms (V.comap (toLp μ).toLinearMap) := by
    rw [formsIn, clsL, Submodule.comap_comp, summandCuspForms]
  have hne := summandCuspForms_ne_bot μ _ hI hirr
  have hcl := topologicalClosure_map_summandCuspForms hc hI hirr hne
  have h1 := summandCuspForms_stable_ρ hc hI
  have h2 := summandCuspForms_stable_σ hI
  have h3 := summandCuspForms_stable_τ hI
  have h4 := fun W hW a b c d => eq_summandCuspForms (W := W) hc hI hirr hW a b c d
  rw [← e] at hne hcl h1 h2 h3 h4
  refine ⟨⟨h1, h2, h3⟩, hne, fun W hW hs => ?_, ?_⟩
  · exact (em (W = ⊥)).imp_right fun h0 => h4 W hW hs.ρ hs.σ hs.τ h0
  · refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_ hV.closed) fun v hv => ?_
    · exact Submodule.map_le_iff_le_comap.2 inf_le_right
    · obtain ⟨u, rfl⟩ : ∃ u : CuspL2 μ, toLp μ u = v := ⟨(⟨v, hV.le hv⟩ : cuspidalL2 μ), rfl⟩
      have hu : u ∈ closure (((formsIn μ V).map (cuspVecL μ) : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) := by
        rw [← Submodule.topologicalClosure_coe, hcl]
        exact hv
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      refine map_mem_closure (toLp μ).continuous hu fun x hx => ?_
      obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hx
      exact Submodule.mem_map_of_mem (f := clsL μ) hφ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.GalCentral
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem galAd_eq_adm {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃+* E)
    (s : Ad E ≃+* Ad E) (h : UpperTheory.CBC.IsGalAd σ s) : s.toRingHom = UpperTheory.V.FieldIso.adm σ :=
  (UpperTheory.ConvolutionTheory.K.adUnique E σ s.toRingHom h.1 h.2.1).trans
    (UpperTheory.ConvolutionTheory.K.adUnique E σ (UpperTheory.V.FieldIso.adm σ) (UpperTheory.V.FieldIso.continuous_adm σ)
      (UpperTheory.V.FieldIso.adm_algebraMap σ)).symm

open Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep in
private theorem cinf_real {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃+* E) (c : ℝ) :
    UpperTheory.V.FieldIso.cinf σ (fun _ => (c : ℂ)) = fun _ => (c : ℂ) := by
  funext u
  change coord _ _ = _
  unfold coord
  split_ifs <;> simp

private theorem map_splitCentre {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃+* E) (a : ℕ)
    (t : ℝ) : UpperTheory.V.FieldIso.gaMap a σ (GlobalTheory.UnitaryBC.splitCentre E a t) = GlobalTheory.UnitaryBC.splitCentre E a t := by
  unfold GlobalTheory.UnitaryBC.splitCentre
  rw [UpperTheory.V.FieldIso.gaMap_infGL]
  congr 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change UpperTheory.V.FieldIso.cinf σ (Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j) =
    Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, ← Complex.ofReal_exp]
    exact cinf_real σ _
  · rw [Matrix.diagonal_apply_ne _ h]
    exact map_zero _

theorem UpperTheory.ConvolutionTheory.Dp.galCentral :
    UpperTheory.ConvolutionTheory.Dp.GalCentral := by
  intro E _ _ _ n σ s h
  refine ⟨fun s' h' => RingEquiv.ext fun x => ?_, fun t => ?_⟩
  · have e := (galAd_eq_adm σ s' h').trans (galAd_eq_adm σ s h).symm
    exact congrArg (fun f : Ad E →+* Ad E => f x) e
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Units.ext (Matrix.ext fun i => i.elim0)
    · have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have ht : t = ⟨Real.exp (n * Module.finrank ℚ E * (Real.log t / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ := by
        refine Subtype.ext ?_
        change (t : ℝ) = Real.exp _
        rw [mul_div_cancel₀ _ (mul_ne_zero hn' hd), Real.exp_log t.2]
      rw [ht, ← UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n, galAd_eq_adm σ s h]
      exact map_splitCentre σ n _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.JGenLinLie
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_along {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z) = UpperTheory.ConvolutionTheory.along τ z := by
  refine Cm.mixed_ext fun w => ?_
  have h : (Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z)).2 w = GlobalTheory.CuspRep.atEmb τ z w.1 := Cm.mixRing_snd _ w
  rw [h, PositivityTheory.Rg.Cz.GK.atEmb_apply]
  simp only [UpperTheory.ConvolutionTheory.along]
  by_cases e : w.1 = InfinitePlace.mk τ
  · rw [if_pos e, if_pos e, e]
  · rw [if_neg e, if_neg e]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) (z : ℂ) :
    Cm.ιC E n (GlobalTheory.CuspRep.toL (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z))) = (1 : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b z := by
  rw [Cm.ιC_apply, UpperTheory.ConvolutionTheory.elem]
  congr 2
  refine Subtype.ext ?_
  change Cm.matEq E n (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z)) = Matrix.single a b (UpperTheory.ConvolutionTheory.along τ z)
  refine Matrix.ext fun i j => ?_
  rw [Cm.matEq_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs
  · exact UpperTheory.ConvolutionTheory.Dp.jGen_along τ z
  · exact map_zero _

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_gen {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) :
    (2⁻¹ : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b 1 - (2⁻¹ * Complex.I) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b Complex.I = Cm.genC τ a b := by
  rw [Cm.genC, AlgRepEndIrreducible.eL, UpperTheory.ConvolutionTheory.Dp.jGen_lie, UpperTheory.ConvolutionTheory.Dp.jGen_lie, TensorProduct.smul_tmul', smul_sub,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one, one_div]

private noncomputable def UpperTheory.ConvolutionTheory.Dp.jGen_lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    HarishChandra.gl n →ₗ[ℂ] A where
  toFun X := ∑ c : Fin n × Fin n, X c.1 c.2 • F c.1 c.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r X := by simp [Finset.smul_sum, mul_smul]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (c : Fin n × Fin n) : UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c) = F c.1 c.2 := by
  change ∑ d : Fin n × Fin n, (HarishChandra.E c) d.1 d.2 • F d.1 d.2 = _
  rw [Finset.sum_eq_single c]
  · simp [HarishChandra.E]
  · intro d _ hd
    have : ¬ (c.1 = d.1 ∧ c.2 = d.2) := fun h => hd (Prod.ext h.1.symm h.2.symm)
    simp [HarishChandra.E, Matrix.single_apply, this]
  · simp

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : HarishChandra.gl n) :
    UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅X, Y⁆ = ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F X, UpperTheory.ConvolutionTheory.Dp.jGen_lin F Y⁆ := by
  have hE : ∀ c d : Fin n × Fin n, UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅HarishChandra.E c, HarishChandra.E d⁆ =
      ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c), UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E d)⁆ := by
    intro c d
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, HarishChandra.E_mul_sub_mul,
      UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, hF, map_sub]
    congr 1 <;> split_ifs <;> simp [UpperTheory.ConvolutionTheory.Dp.jGen_lin_E]
  rw [HarishChandra.eq_sum_E X, HarishChandra.eq_sum_E Y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_ex {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : ∃ f : HarishChandra.U n →ₐ[ℂ] A, ∀ a b, f (HarishChandra.e (a, b)) = F a b := by
  let L : HarishChandra.gl n →ₗ⁅ℂ⁆ A :=
    { UpperTheory.ConvolutionTheory.Dp.jGen_lin F with map_lie' := fun {X Y} => UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie F hF X Y }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ L, fun a b => ?_⟩
  rw [HarishChandra.e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact UpperTheory.ConvolutionTheory.Dp.jGen_lin_E F (a, b)

theorem UpperTheory.ConvolutionTheory.Dp.jGen :
    UpperTheory.ConvolutionTheory.Dp.JGen := by
  intro E _ _ _ n τ
  have key : ∀ j : HarishChandra.U n →ₐ[ℂ] UpperTheory.ConvolutionTheory.UC E n,
      UpperTheory.ConvolutionTheory.IsJ (n := n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b := fun j =>
    ⟨fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b),
      fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b).symm⟩
  obtain ⟨f, hf⟩ := UpperTheory.ConvolutionTheory.Dp.jGen_ex (Cm.genC (a := n) τ) (Cm.glRel_genC τ)
  exact ⟨⟨f, (key f).2 hf⟩, key⟩
end

