module

public import Mathlib
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
public import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
public import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.homConv :
    ∀ (G G₂ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (p : G₂ →* G) (hp : Continuous p)
      (μ : Measure G) [μ.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
      (f : CompactlySupportedContinuousMap G₂ ℂ) (e : CompactlySupportedContinuousMap G ℂ),
      ∃ g : CompactlySupportedContinuousMap G ℂ, (∀ x, g x = ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂) ∧
        tsupport g ⊆ p '' tsupport f * tsupport e ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H),
          π.integrated μ (UnitaryRep.ccToL1 μ g) =
            (π.compHom p hp).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f) ∘L π.integrated μ (UnitaryRep.ccToL1 μ e) := by
  intro G G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp μ _ μ₂ _ f e
  have hf : IsCompact (tsupport f) := f.hasCompactSupport.isCompact
  have hS : IsCompact (p '' tsupport f * tsupport e) :=
    (hf.image hp).mul e.hasCompactSupport.isCompact

  have hker : Continuous fun q : G × G₂ => f q.2 * e ((p q.2)⁻¹ * q.1) :=
    (f.continuous.comp continuous_snd).mul
      (e.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))
  have hz₂ : ∀ (x : G) (y : G₂), y ∉ tsupport f → f y * e ((p y)⁻¹ * x) = 0 := fun x y hy => by
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hz₁ : ∀ (x : G) (y : G₂), x ∉ p '' tsupport f * tsupport e →
      f y * e ((p y)⁻¹ * x) = 0 := fun x y hx => by
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    exact hx ⟨p y, ⟨y, subset_tsupport _ h1, rfl⟩, (p y)⁻¹ * x, subset_tsupport _ h2,
      mul_inv_cancel_left _ _⟩
  have hcont : Continuous fun x : G => ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂ := by
    rw [← continuousOn_univ]
    exact continuousOn_integral_of_compact_support (μ := μ₂)
      (f := fun (x : G) (y : G₂) => f y * e ((p y)⁻¹ * x)) hf hker.continuousOn
      fun x y _ hy => hz₂ x y hy
  have hzero : ∀ x : G, x ∉ p '' tsupport f * tsupport e →
      ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂ = 0 := fun x hx => by
    simp only [hz₁ x _ hx, integral_zero]
  refine ⟨⟨⟨fun x => ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂, hcont⟩, HasCompactSupport.intro hS hzero⟩,
    fun _ => rfl, ?_, ?_⟩
  · refine closure_minimal (fun x hx => ?_) hS.isClosed
    by_contra hx'
    exact hx (hzero x hx')
  · intro H _ _ _ π
    ext v
    rw [ContinuousLinearMap.comp_apply]
    simp only [UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]
    change ∫ x, (∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂) • π x v ∂μ = _
    have hint : Integrable
        (Function.uncurry fun (x : G) (y : G₂) => (f y * e ((p y)⁻¹ * x)) • π x v) (μ.prod μ₂) := by
      refine Continuous.integrable_of_hasCompactSupport
        (hker.smul ((π.continuous_orbit v).comp continuous_fst)) ?_
      refine HasCompactSupport.intro (hS.prod hf) fun q hq => ?_
      have h0 : f q.2 * e ((p q.2)⁻¹ * q.1) = 0 := by
        rcases not_and_or.1 (mt Set.mem_prod.2 hq) with h | h
        · exact hz₁ _ _ h
        · exact hz₂ _ _ h
      change (f q.2 * e ((p q.2)⁻¹ * q.1)) • π q.1 v = 0
      rw [h0, zero_smul]
    have he : Integrable (fun z => e z • π z v) μ :=
      (e.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
        e.hasCompactSupport.smul_right
    simp only [← integral_smul_const]
    rw [integral_integral_swap hint]
    congr 1
    funext y
    rw [← ContinuousLinearMap.integral_comp_comm _ he, ← integral_smul,
      ← integral_mul_left_eq_self _ (p y)]
    simp only [inv_mul_cancel_left, UnitaryRep.map_mul_apply, map_smul, smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtCompact
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.htCompact :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (AdelicGLn.AdelicGL K n)), IsCompact S → ∃ Y : ℝ, 1 ≤ Y ∧ (∀ g ∈ S, AutomorphicForm.height g ≤ Y) ∧
      ∀ (k : ℕ), ∀ g ∈ S ^ k, AutomorphicForm.height g ≤ Y ^ k := by
  intro K _ _ n S hS
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hS
  have hC : 1 ≤ AutomorphicForm.heightConst K n := AutomorphicForm.one_le_heightConst
  have hM1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  have hM' : ∀ g ∈ S, AutomorphicForm.height g ≤ max 1 M := fun g hg =>
    (hM g hg).trans (le_max_right _ _)
  have hY : 1 ≤ AutomorphicForm.heightConst K n * max 1 M :=
    one_le_mul_of_one_le_of_one_le hC hM1
  refine ⟨AutomorphicForm.heightConst K n * max 1 M, hY, fun g hg => ?_, fun k => ?_⟩
  · exact (hM' g hg).trans (le_mul_of_one_le_left (zero_le_one.trans hM1) hC)
  · induction k with
    | zero =>
      intro g hg
      rw [pow_zero, Set.mem_one] at hg
      rw [hg, AutomorphicForm.height_one, pow_zero]
    | succ k ih =>
      intro g hg
      rw [pow_succ] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
      have h1 := ih a ha
      have h2 := hM' b hb
      have hb0 := (AutomorphicForm.height_pos b).le
      have hC0 : 0 ≤ AutomorphicForm.heightConst K n := zero_le_one.trans hC
      have hP0 : 0 ≤ (AutomorphicForm.heightConst K n * max 1 M) ^ k :=
        pow_nonneg (zero_le_one.trans hY) k
      calc AutomorphicForm.height (a * b)
          ≤ AutomorphicForm.heightConst K n * AutomorphicForm.height a * AutomorphicForm.height b :=
            AutomorphicForm.height_mul_le a b
        _ ≤ AutomorphicForm.heightConst K n * (AutomorphicForm.heightConst K n * max 1 M) ^ k
              * max 1 M :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) h2 hb0 (mul_nonneg hC0 hP0)
        _ = (AutomorphicForm.heightConst K n * max 1 M) ^ (k + 1) := by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtProj
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem UpperTheory.ConvolutionTheory.Tf.height_centralSection_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (s : {r : ℝ // 0 < r}) {L : ℝ} (hL : 1 ≤ L) (h1 : (s : ℝ) ≤ L) (h2 : (s : ℝ)⁻¹ ≤ L) :
    AutomorphicForm.height (centralSection K n s) ≤ L ^ (2 * Fintype.card (InfinitePlace K)) := by
  set e : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, ← Nat.cast_mul]
    exact Nat.cast_inv_le_one _
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ L → x ^ e ≤ L := fun x hx hxL =>
    calc x ^ e ≤ L ^ e := Real.rpow_le_rpow hx hxL he0
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL he1
      _ = L := Real.rpow_one L
  refine height_diagUnits_posIdele_le (K := K) (n := n) (ρ := fun _ => (s : ℝ) ^ e)
    (fun _ => Real.rpow_pos_of_pos s.2 e) hL fun _ => ⟨key _ s.2.le h1, ?_⟩
  rw [← Real.inv_rpow s.2.le]
  exact key _ (inv_pos.2 s.2).le h2

theorem UpperTheory.ConvolutionTheory.Tf.htProj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (c : ℕ), 1 ≤ C ∧ ∀ g : AdelicGLn.AdelicGL K n,
      AutomorphicForm.height (retractOne g : AdelicGLn.AdelicGL K n) ≤ C * AutomorphicForm.height g ^ c := by
  intro K _ _ n
  obtain ⟨D, N, -, hD⟩ := UpperTheory.adelicNorm_det_le_height_pow K n
  set m := 2 * Fintype.card (InfinitePlace K) with hm
  have hC : 1 ≤ heightConst K n := one_le_heightConst
  have hD1 : (1 : ℝ) ≤ max 1 D := le_max_left _ _
  refine ⟨heightConst K n * max 1 D ^ m, N * m + 1,
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD1), fun g => ?_⟩
  have hg := one_le_height g
  have hb : ∀ x : AdelicGLn.AdelicGL K n, AutomorphicForm.height x = AutomorphicForm.height g →
      (detModule K n x : ℝ) ≤ max 1 D * AutomorphicForm.height g ^ N := fun x hx => by
    refine (hD x).trans ?_
    rw [hx]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have h2 : (detModule K n g : ℝ)⁻¹ ≤ max 1 D * AutomorphicForm.height g ^ N := by
    have := hb g⁻¹ (height_inv g)
    rwa [map_inv, Positive.coe_inv] at this
  have hz := UpperTheory.ConvolutionTheory.Tf.height_centralSection_le K n (detModule K n g)
    (one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hg)) (hb g rfl) h2
  rw [coe_retractOne]
  refine (height_mul_le _ _).trans ?_
  rw [height_inv]
  calc heightConst K n * AutomorphicForm.height g *
        AutomorphicForm.height (centralSection K n (detModule K n g))
      ≤ heightConst K n * AutomorphicForm.height g * (max 1 D * AutomorphicForm.height g ^ N) ^ m :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped Manifold ContDiff Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_inv {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun fun g => f g⁻¹ := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf (contMDiff_id.inv)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_cont {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  letI := h.chartedSpace
  exact ContMDiff.continuous hf

private theorem UpperTheory.ConvolutionTheory.Tf.deriv_zero {f : G → ℂ} {U : Set G} (hU : IsOpen U) (h0 : ∀ g ∈ U, f g = 0)
    (X : 𝔤) : ∀ g ∈ U, h.rightDeriv X f g = 0 := by
  intro g hg
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := by
    letI := h.chartedSpace
    exact continuous_const.mul h.contMDiff_expG.continuous
  have he : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
    have : (fun Y : 𝔤 => g * h.expG Y) ⁻¹' U ∈ 𝓝 (0 : 𝔤) :=
      (hU.preimage hc).mem_nhds (by simpa using hg)
    filter_upwards [this] with Y hY using h0 _ hY
  simp [IsExpLieAlgebra.rightDeriv, he.fderiv_eq]

private theorem UpperTheory.ConvolutionTheory.Tf.act_zero {U : Set G} (hU : IsOpen U)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    ∀ f : h.smoothFuns (F := ℂ), (∀ g ∈ U, (f : G → ℂ) g = 0) →
      ∀ g ∈ U, (h.rightUAction u f : G → ℂ) g = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro f hf g hg
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, hf g hg, smul_zero]
  | ι x =>
    intro f hf g hg
    show (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) f : G → ℂ) g = 0
    rw [IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
    exact UpperTheory.ConvolutionTheory.Tf.deriv_zero h hU hf _ g hg
  | mul a b iha ihb =>
    intro f hf
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact iha _ (ihb f hf)
  | add a b iha ihb =>
    intro f hf g hg
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, iha f hf g hg,
      ihb f hf g hg, add_zero]

end

theorem UpperTheory.ConvolutionTheory.Tf.invSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (f : archGroup K n → ℂ), f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) →
      (fun g => f g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) ∧ Continuous f ∧ (HasCompactSupport f → (isExpLieAlgebra K n).IsTestFunction f) ∧
      ∀ (hf : f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (u : UEnv K n), tsupport ((isExpLieAlgebra K n).rightUAction u ⟨f, hf⟩ : archGroup K n → ℂ) ⊆ tsupport f := by
  intro K _ _ n f hf
  refine ⟨UpperTheory.ConvolutionTheory.Tf.smooth_inv _ hf, UpperTheory.ConvolutionTheory.Tf.smooth_cont _ hf, fun hc => ⟨hf, hc⟩, fun hf u => ?_⟩
  refine closure_minimal (fun g hg => ?_) (isClosed_tsupport f)
  by_contra hn
  exact hg (UpperTheory.ConvolutionTheory.Tf.act_zero _ (isClosed_tsupport f).isOpen_compl u ⟨f, hf⟩
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) g hn)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

open scoped RestrictedProduct in
private theorem cont_mulSingle {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (A : ∀ i, Subgroup (G i)) (v : ι) : Continuous (RestrictedProduct.mulSingle A v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set ι) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : G v → Πʳ i, [G i, A i]_[Filter.principal ({v}ᶜ : Set ι)] := fun x =>
    ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro i hi
      rw [Pi.mulSingle_eq_of_ne hi]
      exact one_mem _⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem UpperTheory.ConvolutionTheory.Tf.locEmb :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
      Continuous (AdelicGLn.localEmbedding (K := K) (n := n) v) ∧
      (∀ x, finAt v (finEmb K n (AdelicGLn.localEmbedding v x)) = x) ∧
      (∀ w, w ≠ v → ∀ x, finAt w (finEmb K n (AdelicGLn.localEmbedding v x)) = 1) ∧
      (∀ w, w ≠ v → ∀ x y, AdelicGLn.localEmbedding (K := K) (n := n) v x * AdelicGLn.localEmbedding w y =
        AdelicGLn.localEmbedding w y * AdelicGLn.localEmbedding v x) ∧
      ∀ (h : AdelicGLn.FiniteAdelicGL K n), finAt v (finEmb K n h) = 1 → ∀ x,
        AdelicGLn.localEmbedding v x * h = h * AdelicGLn.localEmbedding v x := by
  classical
  intro K _ _ n v
  have e : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
      finAt w (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y w := fun w y => rfl
  have a : ∀ (u w : HeightOneSpectrum (𝓞 K)) x, AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.localEmbedding u x) w =
      Pi.mulSingle (M := fun t : HeightOneSpectrum (𝓞 K) => GL (Fin n) (t.adicCompletion K)) u x w := by
    intro u w x
    change AdelicGLn.finiteRestrictedEquiv K n ((AdelicGLn.finiteRestrictedEquiv K n).symm _) w = _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact RestrictedProduct.coe_mulSingle_apply _ _ _ _
  have c : ∀ (h : AdelicGLn.FiniteAdelicGL K n), finAt v (finEmb K n h) = 1 → ∀ x,
        AdelicGLn.localEmbedding v x * h = h * AdelicGLn.localEmbedding v x := by
    intro h hh x
    apply (AdelicGLn.finiteRestrictedEquiv K n).injective
    refine DFunLike.ext _ _ fun w => ?_
    rw [map_mul, map_mul, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, a]
    by_cases hw : w = v
    · subst hw
      rw [← e, hh, mul_one, one_mul]
    · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
  refine ⟨(AdelicGLn.finiteRestrictedEquiv K n).symm.continuous.comp (cont_mulSingle _ v), fun x => ?_,
    fun w hw x => ?_, fun w hw x y => c _ ?_ x, c⟩
  · rw [e, a, Pi.mulSingle_eq_same]
  · rw [e, a, Pi.mulSingle_eq_of_ne hw]
  · rw [e, a, Pi.mulSingle_eq_of_ne hw.symm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensCont
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.tensCont :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : CompactlySupportedContinuousMap (archGroup K n) ℂ) (e : CompactlySupportedContinuousMap (AdelicGLn.FiniteAdelicGL K n) ℂ),
    (Continuous fun x : normOneGL (K := K) (n := n) => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    (HasCompactSupport fun x : normOneGL (K := K) (n := n) => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    ∀ x : normOneGL (K := K) (n := n), kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
  intro K _ _ n hn β e
  have key : ∀ x : normOneGL (K := K) (n := n), kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
    intro x hx
    have hk := left_ne_zero_of_mul hx
    have he := right_ne_zero_of_mul hx
    obtain ⟨s, hs⟩ : ∃ s, β (infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n s) ≠ 0 := by
      by_contra h0
      simp only [not_exists, ne_eq, not_not] at h0
      exact hk (by simp [kbar, h0])
    refine ⟨_, subset_tsupport _ hs, _, subset_tsupport _ he, ?_⟩
    have hf : ∀ h, MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := fun h => rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul,
      infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  refine ⟨?_, ?_, key⟩
  · exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  · have hC : IsCompact ((fun p : archGroup K n × AdelicGLn.FiniteAdelicGL K n =>
        archP K n p.1 * MultiplicityOne.finProj K n p.2) '' (tsupport β ×ˢ tsupport e)) :=
      (β.hasCompactSupport.isCompact.prod e.hasCompactSupport.isCompact).image
        ((continuous_archP.comp continuous_fst).mul
          (MultiplicityOne.continuous_finProj.comp continuous_snd))
    set_option synthInstance.maxHeartbeats 200000 in
      refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra hne
    obtain ⟨a, ha, h, hh, rfl⟩ := key x hne
    exact hx ⟨(a, h), ⟨ha, hh⟩, rfl⟩
end

