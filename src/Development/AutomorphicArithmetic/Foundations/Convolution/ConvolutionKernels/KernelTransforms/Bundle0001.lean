module

public import Mathlib
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
public import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
public import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
public import GroundTheory.AutomorphicForms.GKModules.ZKFinite
public import GroundTheory.AutomorphicForms.Bundle0006
public import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
public import GroundTheory.AutomorphicForms.Bundle0018
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchHaar

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AdjInt
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.adjInt :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
      (f g : CompactlySupportedContinuousMap G ℂ), (∀ x, g x = conj (f x⁻¹)) →
      ContinuousLinearMap.adjoint (π.integrated μ (UnitaryRep.ccToL1 μ f)) = π.integrated μ (UnitaryRep.ccToL1 μ g) ∧
      ‖π.integrated μ (UnitaryRep.ccToL1 μ f)‖ ≤ ∫ x, ‖f x‖ ∂μ ∧ ∫ x, ‖g x‖ ∂μ = ∫ x, ‖f x‖ ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ π μ _ _ f g hg
  have hf1 : ((UnitaryRep.ccToL1 μ f : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] f := by
    unfold UnitaryRep.ccToL1
    exact MemLp.coeFn_toLp _
  have hg1 : ((UnitaryRep.ccToL1 μ g : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] g := by
    unfold UnitaryRep.ccToL1
    exact MemLp.coeFn_toLp _
  refine ⟨?_, ?_, ?_⟩
  · rw [UnitaryRep.adjoint_integrated]
    congr 1
    apply Lp.ext
    have h2 : (fun x => (UnitaryRep.ccToL1 μ f : G →₁[μ] ℂ) x⁻¹) =ᵐ[μ] fun x => f x⁻¹ :=
      (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae_eq_comp hf1
    filter_upwards [UnitaryRep.coeFn_involution μ (UnitaryRep.ccToL1 μ f), h2, hg1] with x h1 h2 h3
    rw [h1, h2, h3, hg]
  · refine (π.norm_integrated_le μ _).trans (le_of_eq ?_)
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (hf1.mono fun x hx => by simp only [hx])
  · rw [← integral_inv_eq_self (fun x => ‖f x‖) μ]
    congr 1
    ext x
    rw [hg, RCLike.norm_conj]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterC
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem centerC_ex (A : Type) [Ring A] [Algebra ℝ A] (z : ℂ ⊗[ℝ] A) :
    ∃ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c x =>
    refine ⟨c.re • x, c.im • x, ?_⟩
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    refine ⟨a + c, b + d, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

private theorem centerC_uniq (A : Type) [Ring A] [Algebra ℝ A] (a b c d : A)
    (h : (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b = (1 : ℂ) ⊗ₜ[ℝ] c + Complex.I ⊗ₜ[ℝ] d) :
    a = c ∧ b = d := by
  have h1 := congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.reLm w)) h
  have h2 := congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.imLm w)) h
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem UpperTheory.ConvolutionTheory.Tf.centerC :
    ∀ (A : Type) [Ring A] [Algebra ℝ A] (z : ℂ ⊗[ℝ] A), (∃ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b) ∧
      ∀ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b →
        (z ∈ Subalgebra.center ℂ (ℂ ⊗[ℝ] A) ↔ a ∈ Subalgebra.center ℝ A ∧ b ∈ Subalgebra.center ℝ A) := by
  intro A _ _ z
  refine ⟨centerC_ex A z, ?_⟩
  rintro a b rfl
  simp only [Subalgebra.mem_center_iff]
  constructor
  · intro h
    have key : ∀ x : A, x * a = a * x ∧ x * b = b * x := by
      intro x
      have hx := h ((1 : ℂ) ⊗ₜ[ℝ] x)
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hx
      exact centerC_uniq A _ _ _ _ hx
    exact ⟨fun x => (key x).1, fun x => (key x).2⟩
  · rintro ⟨ha, hb⟩ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ha x, hb x,
        mul_comm c Complex.I]
    | add x y hx hy => rw [add_mul, mul_add (_ + _) x y, hx, hy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterTr
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
variable {U : Type*} [Ring U] [Algebra ℝ U]

private def UpperTheory.ConvolutionTheory.Tf.Crv (A : ℝ → U) (D : U) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ → ℝ) (c' : ι → ℝ) (v : ι → U),
    (∀ i, HasDerivAt (c i) (c' i) 0) ∧ (∀ t, A t = ∑ i, c i t • v i) ∧ D = ∑ i, c' i • v i

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.const (u : U) : UpperTheory.ConvolutionTheory.Tf.Crv (fun _ => u) (0 : U) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ => 0, fun _ => u, fun _ => hasDerivAt_const _ _,
    by simp, by simp⟩

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.add {A B : ℝ → U} {D E : U} (hA : UpperTheory.ConvolutionTheory.Tf.Crv A D)
    (hB : UpperTheory.ConvolutionTheory.Tf.Crv B E) : UpperTheory.ConvolutionTheory.Tf.Crv (fun t => A t + B t) (D + E) := by
  obtain ⟨ι, _, c, c', v, hc, hA', rfl⟩ := hA
  obtain ⟨κ, _, d, d', w, hd, hB', rfl⟩ := hB
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c d, Sum.elim c' d', Sum.elim v w, ?_, fun t => ?_, ?_⟩
  · rintro (i | j)
    · exact hc i
    · exact hd j
  · simp [Fintype.sum_sum_type, hA', hB']
  · simp [Fintype.sum_sum_type]

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.mul {A B : ℝ → U} {D E : U} (hA : UpperTheory.ConvolutionTheory.Tf.Crv A D)
    (hB : UpperTheory.ConvolutionTheory.Tf.Crv B E) :
    UpperTheory.ConvolutionTheory.Tf.Crv (fun t => A t * B t) (D * B 0 + A 0 * E) := by
  obtain ⟨ι, _, c, c', v, hc, hA', rfl⟩ := hA
  obtain ⟨κ, _, d, d', w, hd, hB', rfl⟩ := hB
  refine ⟨ι × κ, inferInstance, fun p t => c p.1 t * d p.2 t,
    fun p => c' p.1 * d p.2 0 + c p.1 0 * d' p.2, fun p => v p.1 * w p.2,
    fun p => (hc p.1).mul (hd p.2), fun t => ?_, ?_⟩
  · beta_reduce
    rw [hA', hB', Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [smul_mul_smul_comm]
  · rw [hA' 0, hB' 0, Finset.sum_mul_sum, Finset.sum_mul_sum, Fintype.sum_prod_type,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_smul, smul_mul_smul_comm, smul_mul_smul_comm]

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.lin {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [FiniteDimensional ℝ M] (L : M →ₗ[ℝ] U) {φ : ℝ → M} {φ' : M} (hφ : HasDerivAt φ φ' 0) :
    UpperTheory.ConvolutionTheory.Tf.Crv (fun t => L (φ t)) (L φ') := by
  let b := Module.finBasis ℝ M
  have hsum : ∀ m : M, L m = ∑ i, b.coord i m • L (b i) := fun m => by
    calc L m = L (∑ i, b.repr m i • b i) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, Module.Basis.coord_apply]
  refine ⟨_, inferInstance, fun i t => b.coord i (φ t), fun i => b.coord i φ', fun i => L (b i),
    fun i => ?_, fun t => ?_, ?_⟩
  · exact (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt 0 hφ
  · exact hsum _
  · exact hsum _

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.deriv {A : ℝ → U} {D : U} (hA : UpperTheory.ConvolutionTheory.Tf.Crv A D)
    (l : U →ₗ[ℝ] ℝ) : HasDerivAt (fun t => l (A t)) (l D) 0 := by
  obtain ⟨ι, _, c, c', v, hc, hA', rfl⟩ := hA
  have e : (fun t => l (A t)) = fun t => ∑ i, c i t * l (v i) := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hA', map_sum]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  exact HasDerivAt.fun_sum fun i _ => (hc i).mul_const _

end

section
attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private noncomputable def UpperTheory.ConvolutionTheory.Tf.iotaL :
    𝔤 →ₗ[ℝ] UniversalEnvelopingAlgebra ℝ h.lieSubalgebra where
  toFun Y := UniversalEnvelopingAlgebra.ι ℝ (h.toLie Y)
  map_add' X Y := by
    show UniversalEnvelopingAlgebra.ι ℝ (h.toLie X + h.toLie Y) = _
    exact map_add _ _ _
  map_smul' r X := by
    show UniversalEnvelopingAlgebra.ι ℝ (r • h.toLie X) = _
    exact map_smul _ _ _

private theorem UpperTheory.ConvolutionTheory.Tf.crv_AdU (X : 𝔤) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    UpperTheory.ConvolutionTheory.Tf.Crv (fun t : ℝ => h.AdU (h.expG (t • X)) u)
      (UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * u -
        u * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X)) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, Algebra.commutes, sub_self]
    exact UpperTheory.ConvolutionTheory.Tf.Crv.const _
  | ι x =>
    have e : UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x) =
        UniversalEnvelopingAlgebra.ι ℝ x := rfl
    rw [e]
    simp only [IsExpLieAlgebra.AdU_ι]
    have key := UpperTheory.ConvolutionTheory.Tf.Crv.lin (UpperTheory.ConvolutionTheory.Tf.iotaL h) (h.hasDerivAt_Ad_expG X (h.ofLie x))
    have e2 : UpperTheory.ConvolutionTheory.Tf.iotaL h (h.bracket X (h.ofLie x)) =
        UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * UniversalEnvelopingAlgebra.ι ℝ x -
          UniversalEnvelopingAlgebra.ι ℝ x * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) := by
      show UniversalEnvelopingAlgebra.ι ℝ ⁅h.toLie X, x⁆ = _
      rw [LieHom.map_lie, Ring.lie_def]
    rw [e2] at key
    exact key
  | mul a b ha hb =>
    have key := ha.mul hb
    simp only [map_mul]
    have e0 : ∀ w, h.AdU (h.expG ((0 : ℝ) • X)) w = w := by
      intro w
      rw [zero_smul, h.expG_zero, h.AdU_one, AlgHom.id_apply]
    simp only [e0] at key
    convert key using 1
    noncomm_ring
  | add a b ha hb =>
    have key := ha.add hb
    simp only [map_add (f := _)]
    convert key using 1
    noncomm_ring

private theorem UpperTheory.ConvolutionTheory.Tf.AdU_expG {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) (X : 𝔤) : h.AdU (h.expG X) z = z := by
  have hc : UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * z -
      z * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) = 0 :=
    sub_eq_zero.2 (Subalgebra.mem_center_iff.1 hz _)
  have hcrv := UpperTheory.ConvolutionTheory.Tf.crv_AdU h X z
  rw [hc] at hcrv
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℝ _).1 fun l => ?_
  set c : ℝ → ℝ := fun t => l (h.AdU (h.expG (t • X)) z) with hcdef
  have hderiv : ∀ t, HasDerivAt c 0 t := by
    intro t
    have h1 := hcrv.deriv (l ∘ₗ (h.AdU (h.expG (t • X))).toLinearMap)
    simp only [map_zero] at h1
    have h2 : HasDerivAt (fun s : ℝ => l ((h.AdU (h.expG (t • X))).toLinearMap
        (h.AdU (h.expG ((s - t) • X)) z))) 0 t := by
      have h1' : HasDerivAt (fun s : ℝ => l ((h.AdU (h.expG (t • X))).toLinearMap
          (h.AdU (h.expG (s • X)) z))) 0 (t - t) := by
        rw [sub_self]; exact h1
      exact h1'.comp_sub_const t t
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show l (h.AdU (h.expG (s • X)) z) = l (h.AdU (h.expG (t • X)) (h.AdU (h.expG ((s - t) • X)) z))
    rw [← AlgHom.comp_apply, ← h.AdU_mul, ← h.expG_add_smul, add_sub_cancel]
  have hconst : c 1 = c 0 :=
    is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) 1 0
  simp only [hcdef, one_smul, zero_smul, h.expG_zero, h.AdU_one, AlgHom.id_apply] at hconst
  rw [map_sub, hconst, sub_self]

private theorem UpperTheory.ConvolutionTheory.Tf.AdU_closure {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) {k : G} (hk : k ∈ Subgroup.closure (Set.range h.expG)) :
    h.AdU k z = z := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact UpperTheory.ConvolutionTheory.Tf.AdU_expG h hz X
  | one => rw [h.AdU_one, AlgHom.id_apply]
  | mul x y _ _ hx hy => rw [h.AdU_mul, AlgHom.comp_apply, hy, hx]
  | inv x _ hx =>
    have := h.AdU_inv_apply x z
    rwa [hx] at this

end

theorem UpperTheory.ConvolutionTheory.Tf.centerTr :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (z : UEnv K n), z ∈ (isExpLieAlgebra K n).centerU → ∀ k ∈ Subgroup.closure (Set.range (isExpLieAlgebra K n).expG),
      ∀ (f : archGroup K n → ℂ) (hf : f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), ∃ hk : (fun g => f (g * k)) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ g,
        ((isExpLieAlgebra K n).rightUAction z ⟨_, hk⟩ : archGroup K n → ℂ) g = ((isExpLieAlgebra K n).rightUAction z ⟨f, hf⟩ : archGroup K n → ℂ) (g * k) := by
  intro K _ _ n z hz k hk f hf
  refine ⟨(isExpLieAlgebra K n).isSmoothFun_rightTranslate hf k, fun g => ?_⟩
  have hinv : (isExpLieAlgebra K n).AdU k⁻¹ z = z :=
    UpperTheory.ConvolutionTheory.Tf.AdU_closure _ hz (Subgroup.inv_mem _ hk)
  have e := LinearMap.congr_fun
    ((isExpLieAlgebra K n).rightUAction_comp_rightTranslate (F := ℂ) k z) ⟨f, hf⟩
  rw [hinv] at e
  exact congrFun (congrArg Subtype.val e) g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommInt
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.commInt :
    ∀ (G G₁ G₂ H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : UnitaryRep G H) (p₁ : G₁ →* G) (h₁ : Continuous p₁) (p₂ : G₂ →* G) (h₂ : Continuous p₂)
      (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
      (f₁ : CompactlySupportedContinuousMap G₁ ℂ) (f₂ : CompactlySupportedContinuousMap G₂ ℂ),
      (∀ w v : H, ⟪w, (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁)
          ((π.compHom p₂ h₂).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f₂) v)⟫_ℂ =
        ∫ a, ∫ b, f₁ a * f₂ b * ⟪w, π (p₁ a * p₂ b) v⟫_ℂ ∂μ₂ ∂μ₁) ∧
      ((∀ a b, p₁ a * p₂ b = p₂ b * p₁ a) →
        (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁) ∘L (π.compHom p₂ h₂).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f₂) =
        (π.compHom p₂ h₂).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f₂) ∘L (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁)) := by
  intro G G₁ G₂ H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π p₁ h₁ p₂ h₂ μ₁ _ μ₂ _ f₁ f₂
  have key : ∀ {L : Type} [Group L] [TopologicalSpace L] [MeasurableSpace L] [BorelSpace L] (σ : UnitaryRep L H) (μ : Measure L)
      [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap L ℂ) (w u : H),
      ⟪w, σ.integrated μ (UnitaryRep.ccToL1 μ f) u⟫_ℂ = ∫ g, f g * ⟪w, σ g u⟫_ℂ ∂μ := by
    intro L _ _ _ _ σ μ _ f w u
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 μ f).mono fun g hg => ?_)
    exact congrArg (· * ⟪w, σ g u⟫_ℂ) hg
  refine ⟨fun w v => ?_, fun hc => ?_⟩
  · rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    dsimp only
    rw [UnitaryRep.compHom_apply, UnitaryRep.inner_map_right, key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    rw [UnitaryRep.compHom_apply, UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply, mul_assoc]
  · have step : ∀ b, π (p₂ b) ∘L (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁) =
        (π.compHom p₁ h₁).integrated μ₁ (UnitaryRep.ccToL1 μ₁ f₁) ∘L π (p₂ b) := fun b => by
      refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
      intro a v
      simp only [UnitaryRep.compHom_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hc]
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro b v
    exact (DFunLike.congr_fun (step b) v).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.DerivInt
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem UpperTheory.ConvolutionTheory.Tf.rightAction_integral_derivative {Θ : G → ℂ} (hΘ : Continuous Θ)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (κ : h.smoothFuns (F := ℂ))
    (hκ : h.IsTestFunction (fun y => (κ : G → ℂ) y⁻¹)) :
    h.IsTestFunction (fun y => (h.rightUAction u κ : G → ℂ) y⁻¹) ∧
      (h.rightUAction (F := ℂ) u
          ⟨fun g => ∫ y, Θ (g * y) * (κ : G → ℂ) y⁻¹ ∂μ, h.isSmoothFun_integral_mul μ hΘ hκ⟩ : G → ℂ) =
        fun g => ∫ y, Θ (g * y) * (h.rightUAction u κ : G → ℂ) y⁻¹ ∂μ := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing κ with
  | algebraMap r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    refine ⟨hκ.const_mul (r : ℂ), ?_⟩
    funext g
    exact (IsExpLieAlgebra.integral_mul_const_mul μ Θ (fun y => (κ : G → ℂ) y⁻¹) (r : ℂ) g).symm
  | ι x =>
    have e : UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x) =
        UniversalEnvelopingAlgebra.ι ℝ x := rfl
    have e2 : (fun y => h.rightDeriv (h.ofLie x) (κ : G → ℂ) y⁻¹) =
        h.convDeriv (h.ofLie x) (fun y => (κ : G → ℂ) y⁻¹) := by
      funext y
      simp [IsExpLieAlgebra.convDeriv]
    simp only [e, IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
    refine ⟨e2 ▸ hκ.convDeriv _, ?_⟩
    funext g
    rw [h.rightDeriv_integral_mul μ hΘ hκ, ← e2]
  | mul a b ha hb =>
    obtain ⟨hb1, hb2⟩ := hb κ hκ
    obtain ⟨ha1, ha2⟩ := ha _ hb1
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨ha1, ?_⟩
    rw [← ha2]
    congr 2
    exact Subtype.ext hb2
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha κ hκ
    obtain ⟨hb1, hb2⟩ := hb κ hκ
    simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add]
    refine ⟨ha1.add hb1, ?_⟩
    rw [ha2, hb2]
    funext g
    exact (h.integral_mul_add μ hΘ ha1 hb1 g).symm

private theorem UpperTheory.ConvolutionTheory.Tf.derivInt_shift (κ Θ : G → ℂ) (x : G) :
    ∫ a, κ (a⁻¹ * x) * Θ a ∂μ = ∫ y, Θ (x * y) * κ y⁻¹ ∂μ := by
  rw [← integral_mul_left_eq_self (μ := μ) (fun a => κ (a⁻¹ * x) * Θ a) x]
  congr 1
  funext y
  simp [mul_comm]

end

theorem UpperTheory.ConvolutionTheory.Tf.derivInt :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (κ : archGroup K n → ℂ) (hκ : κ ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), HasCompactSupport κ →
      ∀ Θ : archGroup K n → ℂ, Continuous Θ →
      ∃ hF : (fun x => ∫ a, κ (a⁻¹ * x) * Θ a ∂ν) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ (u : UEnv K n) (x : archGroup K n),
        ((isExpLieAlgebra K n).rightUAction u ⟨_, hF⟩ : archGroup K n → ℂ) x =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨κ, hκ⟩ : archGroup K n → ℂ) (a⁻¹ * x) * Θ a ∂ν := by
  intro K _ _ n ν _ κ hκ hc Θ hΘ
  have ht : (isExpLieAlgebra K n).IsTestFunction (fun y => κ y⁻¹) :=
    ⟨IsExpLieAlgebra.isSmoothFun_comp_inv hκ, hc.comp_homeomorph (Homeomorph.inv _)⟩
  have e : (fun x => ∫ a, κ (a⁻¹ * x) * Θ a ∂ν) = fun x => ∫ y, Θ (x * y) * κ y⁻¹ ∂ν :=
    funext fun x => UpperTheory.ConvolutionTheory.Tf.derivInt_shift ν κ Θ x
  have hs := (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΘ ht
  refine ⟨e ▸ hs, fun u x => ?_⟩
  have key := (UpperTheory.ConvolutionTheory.Tf.rightAction_integral_derivative (isExpLieAlgebra K n) ν hΘ u ⟨κ, hκ⟩ ht).2
  rw [UpperTheory.ConvolutionTheory.Tf.derivInt_shift ν _ Θ x, ← congrFun key x]
  exact congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
    archGroup K n → ℂ) x) (Subtype.ext e)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.unimod :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure], ν.IsMulRightInvariant ∧ ν.IsInvInvariant) ∧
      ∀ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], m.IsMulRightInvariant ∧ m.IsInvInvariant := by
  intro K _ _ n
  refine ⟨fun ν _ => ⟨isMulRightInvariant_archGroup ν, isInvInvariant_archGroup ν⟩, fun m _ => ?_⟩
  haveI hr : m.IsMulRightInvariant := Whittaker.isMulRightInvariant_finite K n m
  exact ⟨hr, ⟨inv_eq_self_of_isMulRightInvariant m⟩⟩
end

