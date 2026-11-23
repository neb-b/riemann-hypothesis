module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
public import GroundTheory.AutomorphicForms.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem commute_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ (∀ v, ∀ w ∈ V, ⟪v - prj V v, w⟫_ℂ = 0) ∧ Commute T (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  have a1 : ∀ v, prj V v ∈ V := fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v)
  have a3 : ∀ v, ∀ w ∈ V, ⟪v - prj V v, w⟫_ℂ = 0 := fun v w hw =>
    Submodule.starProjection_inner_eq_zero v w ((hm _).2 hw)
  refine ⟨a1, fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), a3, ?_⟩
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 (h1 _ (a1 v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact a3 v _ (h2 w ((hm _).1 hw))

theorem UpperTheory.ConvolutionTheory.Tf.commPrj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
      IsClosed (fixF μ U : Set (LL μ)) ∧ (∀ v, v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v) ∧ (∀ v, prj (fixF μ U) v ∈ fixF μ U) ∧
      (∀ v ∈ fixF μ U, prj (fixF μ U) v = v) ∧ (∀ u ∈ U, rhoF μ u ∘L prj (fixF μ U) = prj (fixF μ U) ∧ prj (fixF μ U) ∘L rhoF μ u = prj (fixF μ U)) ∧
      (∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h') ∧ rhoF μ 1 = 1 ∧ (∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹) ∧
      ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → Commute T (prj (fixF μ U)) := by
  intro K _ _ n μ _ U
  have hmem : ∀ v, v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v := fun v => by
    simp only [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  have hcl : IsClosed (fixF μ U : Set (LL μ)) := by
    have : (fixF μ U : Set (LL μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v} := by
      ext v
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := fun h h' => by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [rhoF, map_mul, UnitaryRep.map_mul_apply, ContinuousLinearMap.comp_apply]
  have hone : rhoF μ 1 = 1 := by
    simp only [rhoF, map_one, UnitaryRep.map_one]
  have hadj : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := fun h => by
    unfold rhoF
    rw [UnitaryRep.adjoint_map, map_inv (MultiplicityOne.finProj K n)]
  have hpres : ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → ∀ v ∈ fixF μ U, T v ∈ fixF μ U := by
    intro T hT v hv
    rw [hmem] at hv ⊢
    intro u hu
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hT u hu).eq
    simp only [ContinuousLinearMap.mul_apply, hv u hu] at this
    exact this.symm
  have hT : ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → Commute T (prj (fixF μ U)) := by
    intro T hT
    refine (commute_prj _ hcl T (hpres T hT) (hpres _ fun u hu => ?_)).2.2.2
    have := (hT u⁻¹ (U.inv_mem hu)).star_star
    rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hadj, inv_inv] at this
  obtain ⟨a1, a2, -, -⟩ := commute_prj _ hcl 0 (fun v _ => by simp) (fun v _ => by simp)
  have hl : ∀ u ∈ U, rhoF μ u ∘L prj (fixF μ U) = prj (fixF μ U) := fun u hu =>
    ContinuousLinearMap.ext fun v => (hmem _).1 (a1 v) u hu
  refine ⟨hcl, hmem, a1, a2, fun u hu => ⟨hl u hu, ?_⟩, hmul, hone, hadj, hT⟩
  have hfix : ∀ u ∈ U, ∀ v ∈ fixF μ U, rhoF μ u v ∈ fixF μ U := fun u hu v hv => by
    rw [(hmem v).1 hv u hu]; exact hv
  have hc := (commute_prj _ hcl (rhoF μ u) (hfix u hu) (by rw [hadj]; exact hfix _ (U.inv_mem hu))).2.2.2
  exact hc.eq.symm.trans (hl u hu)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvOf
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.evOf :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι κ : Type) (a : ι → A) (b : κ → A) (S : Subalgebra ℂ A),
      (∀ i j, Commute (a i) (a j)) → (∀ i k, Commute (a i) (b k)) → (∀ k l, Commute (b k) (b l)) → (∀ i, a i ∈ S) → (∀ k, b k ∈ S) →
      ∃ ev : MvPolynomial κ (MvPolynomial ι ℂ) →+* A, (∀ c : ℂ, ev (C (C c)) = c • 1) ∧ (∀ i, ev (C (X i)) = a i) ∧
        (∀ k, ev (X k) = b k) ∧ ∀ P, ev P ∈ S := by
  intro A _ _ ι κ a b S haa hab hbb haS hbS
  have hcomm : ∀ x ∈ Set.range a ∪ Set.range b, ∀ y ∈ Set.range a ∪ Set.range b,
      x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨k, rfl⟩) y (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact (haa i j).eq
    · exact (hab i l).eq
    · exact (hab j k).symm.eq
    · exact (hbb k l).eq
  have hle : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) ≤ S := by
    apply Algebra.adjoin_le
    rintro x (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact haS i
    · exact hbS k
  have hmc : ∀ x y : Algebra.adjoin ℂ (Set.range a ∪ Set.range b), x * y = y * x := by
    intro x y
    apply Subtype.ext
    have h1 : ∀ z ∈ Set.range a ∪ Set.range b, Commute z (y : A) := fun z hz =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute y.2 (fun w hw => hcomm z hz w hw)
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute x.2
      (fun w hw => (h1 w hw).symm)).symm.eq
  letI : CommRing (Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) :=
    { (inferInstance : Ring (Algebra.adjoin ℂ (Set.range a ∪ Set.range b))) with
      mul_comm := hmc }
  let a' : ι → Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : κ → Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    fun k => ⟨b k, Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)⟩
  let e : MvPolynomial κ (MvPolynomial ι ℂ) →+* Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    eval₂Hom (eval₂Hom (algebraMap ℂ _) a') b'
  refine ⟨(Algebra.adjoin ℂ (Set.range a ∪ Set.range b)).val.toRingHom.comp e, ?_, ?_, ?_, ?_⟩
  · intro c
    show ((e (C (C c)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_C]
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  · intro i
    show ((e (C (X i)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_C, eval₂Hom_X']
    rfl
  · intro k
    show ((e (X k) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_X']
    rfl
  · intro P
    exact hle (e P).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem rUC_tmul (c : ℂ) (a : UEnv K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
    rUC (c ⊗ₜ[ℝ] a) f = c • (isExpLieAlgebra K n).rightUAction a f := by
  exact congrArg (fun T : Module.End ℂ ((isExpLieAlgebra K n).smoothFuns (F := ℂ)) => T f)
    (Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ _) (isExpLieAlgebra K n).rightUAction
      (fun c _ => Algebra.commute_algebraMap_left c _) c a)

private theorem tsupport_rUC (u : UC K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
    tsupport (rUC u f : archGroup K n → ℂ) ⊆ tsupport (f : archGroup K n → ℂ) := by
  induction u using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, Submodule.coe_zero]
    simp
  | tmul c a =>
    rw [rUC_tmul, Submodule.coe_smul]
    refine subset_trans ?_ ((UpperTheory.ConvolutionTheory.Tf.invSmooth K n f f.2).2.2.2 f.2 a)
    exact tsupport_smul_subset_right (fun _ => c) _
  | add u v hu hv =>
    rw [map_add (f := _), LinearMap.add_apply, Submodule.coe_add]
    exact (tsupport_add _ _).trans (Set.union_subset hu hv)

private theorem tsupport_inv_subset {f f' : archGroup K n → ℂ} (h : tsupport f ⊆ tsupport f') :
    tsupport (fun g => f g⁻¹) ⊆ tsupport (fun g => f' g⁻¹) := by
  have e : ∀ φ : archGroup K n → ℂ, tsupport (fun g => φ g⁻¹) = (Homeomorph.inv (archGroup K n)) ⁻¹' tsupport φ := by
    intro φ
    rw [tsupport, tsupport, Homeomorph.preimage_closure]
    rfl
  rw [e, e]
  exact Set.preimage_mono h

private theorem smooth_inv {β : TI K n} (hβ : SmoothT β) :
    (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) :=
  (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1

private theorem tsupport_rightUniversal {β : TI K n} (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (u : UC K n) :
    tsupport (fun g => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) ⊆ tsupport β := by
  have := tsupport_inv_subset (tsupport_rUC u ⟨fun g => β g⁻¹, h⟩)
  simpa only [inv_inv] using this

private theorem lact_apply {β : TI K n} (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (u : UC K n) (g : archGroup K n) :
    lact u β g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ := by
  have hc : Continuous (fun g : archGroup K n => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) :=
    (UpperTheory.ConvolutionTheory.Tf.invSmooth K n _ (rUC u ⟨fun g => β g⁻¹, h⟩).2).2.1.comp continuous_inv
  have hs : HasCompactSupport (fun g : archGroup K n => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) :=
    β.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_rightUniversal h u)
  have H : ∃ (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (γ : TI K n),
      ∀ g, γ g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ :=
    ⟨h, ⟨⟨_, hc⟩, hs⟩, fun _ => rfl⟩
  rw [lact, dite_eq_left H]
  exact H.choose_spec.choose_spec g

private theorem lact_smooth {β : TI K n} (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (u : UC K n) : SmoothT (lact u β) := by
  have e : (fun g => lact u β g) = fun g => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ :=
    funext (lact_apply h u)
  rw [SmoothT, e]
  exact (isExpLieAlgebra K n).mem_smoothFuns.1
    (UpperTheory.ConvolutionTheory.Tf.invSmooth K n _ (rUC u ⟨fun g => β g⁻¹, h⟩).2).1

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Tf.lactSpec :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (β : TI K n), SmoothT β → ∃ h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ),
      (∀ (u : UC K n) (g : archGroup K n), lact u β g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹) ∧
      (∀ u, SmoothT (lact u β) ∧ tsupport (lact u β) ⊆ tsupport β) ∧ lact 1 β = β ∧
      (∀ u v, lact (u * v) β = lact u (lact v β) ∧ lact (u + v) β = lact u β + lact v β) ∧
      (∀ (c : ℂ) u, lact (c • u) β = c • lact u β ∧ lact u (c • β) = c • lact u β) ∧
      (∀ β', SmoothT β' → SmoothT (β + β') ∧ ∀ u, lact u (β + β') = lact u β + lact u β') ∧
      ∀ (a : UEnv K n) (g : archGroup K n), lact ((1 : ℂ) ⊗ₜ[ℝ] a) β g =
        ((isExpLieAlgebra K n).rightUAction a ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ := by
  intro K _ _ n β hβ
  have h := smooth_inv hβ
  refine ⟨h, lact_apply h, fun u => ⟨lact_smooth h u, ?_⟩, ?_, fun u v => ⟨?_, ?_⟩, fun c u => ⟨?_, ?_⟩,
    fun β' hβ' => ⟨?_, fun u => ?_⟩, fun a g => ?_⟩
  · have e : (lact u β : archGroup K n → ℂ) = fun g => (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ :=
      funext (lact_apply h u)
    rw [e]
    exact tsupport_rightUniversal h u
  · ext g
    rw [lact_apply h, map_one, Module.End.one_apply]
    simp only [inv_inv]
  · ext g
    have h' := smooth_inv (lact_smooth h v)
    have e : (⟨fun g => lact v β g⁻¹, h'⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        rUC v ⟨fun g => β g⁻¹, h⟩ :=
      Subtype.ext (funext fun x => by rw [← inv_inv x, ← lact_apply h v, inv_inv])
    rw [lact_apply h, lact_apply h', e, map_mul, Module.End.mul_apply]
  · ext g
    rw [CompactlySupportedContinuousMap.add_apply, lact_apply h, lact_apply h, lact_apply h, map_add (f := _),
      LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  · ext g
    rw [CompactlySupportedContinuousMap.smul_apply, lact_apply h, lact_apply h, map_smul,
      LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  · ext g
    have h' : (fun g => (c • β) g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) :=
      Submodule.smul_mem _ c h
    have e : (⟨fun g => (c • β) g⁻¹, h'⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        c • ⟨fun g => β g⁻¹, h⟩ := rfl
    rw [CompactlySupportedContinuousMap.smul_apply, lact_apply h', lact_apply h, e, map_smul,
      Submodule.coe_smul, Pi.smul_apply]
  · exact (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.add_mem _
      ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ'))
  · ext g
    have h₂ := smooth_inv hβ'
    have h' : (fun g => (β + β') g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) :=
      Submodule.add_mem _ h h₂
    have e : (⟨fun g => (β + β') g⁻¹, h'⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        ⟨fun g => β g⁻¹, h⟩ + ⟨fun g => β' g⁻¹, h₂⟩ := rfl
    rw [CompactlySupportedContinuousMap.add_apply, lact_apply h', lact_apply h, lact_apply h₂, e, map_add (f := _),
      Submodule.coe_add, Pi.add_apply]
  · rw [lact_apply h, rUC_tmul, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem ccToL1_smul {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (c : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 μ (c • f) = c • UnitaryRep.ccToL1 μ f := by
  unfold UnitaryRep.ccToL1
  rw [← MemLp.toLp_const_smul]
  rfl

private theorem norm_int_le {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ) :
    ‖π.integrated μ (UnitaryRep.ccToL1 μ f)‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  have hf1 : ((UnitaryRep.ccToL1 μ f : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] f := by
    unfold UnitaryRep.ccToL1
    exact MemLp.coeFn_toLp _
  refine (π.norm_integrated_le μ _).trans (le_of_eq ?_)
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hf1.mono fun x hx => by simp only [hx])

private theorem int_add {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g : CompactlySupportedContinuousMap G ℂ) :
    π.integrated μ (UnitaryRep.ccToL1 μ (f + g)) =
      π.integrated μ (UnitaryRep.ccToL1 μ f) + π.integrated μ (UnitaryRep.ccToL1 μ g) := by
  rw [UnitaryRep.ccToL1_add, map_add (f := _)]

private theorem int_smul {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (c : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    π.integrated μ (UnitaryRep.ccToL1 μ (c • f)) = c • π.integrated μ (UnitaryRep.ccToL1 μ f) := by
  rw [ccToL1_smul, map_smul]

private theorem int_commute {G G₁ H : Type} [Group G] [TopologicalSpace G] [Group G₁] [TopologicalSpace G₁]
    [MeasurableSpace G₁] [OpensMeasurableSpace G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (p : G₁ →* G) (hp : Continuous p) (μ : Measure G₁) [IsFiniteMeasureOnCompacts μ]
    (f : G₁ →₁[μ] ℂ) (x : G) (hx : ∀ a, x * p a = p a * x) :
    Commute ((π.compHom p hp).integrated μ f) (π x) := by
  have hT : π x ∈ (π.compHom p hp).intertwiners (π.compHom p hp) := by
    intro a v
    show π x (π (p a) v) = π (p a) (π x v)
    rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hx]
  exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ μ hT f).symm

theorem UpperTheory.ConvolutionTheory.Tf.opAlg :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure],
      (∀ β β' : TI K n, Oinf μ ν (conv ν β β') = Oinf μ ν β ∘L Oinf μ ν β' ∧ Oinf μ ν (β + β') = Oinf μ ν β + Oinf μ ν β') ∧
      (∀ e e' : TF K n, Ofin μ m (conv m e e') = Ofin μ m e ∘L Ofin μ m e' ∧ Ofin μ m (e + e') = Ofin μ m e + Ofin μ m e') ∧
      (∀ (c : ℂ) (β : TI K n) (e : TF K n), Oinf μ ν (c • β) = c • Oinf μ ν β ∧ Ofin μ m (c • e) = c • Ofin μ m e) ∧
      (∀ β β' : TI K n, (∀ x, β' x = conj (β x⁻¹)) → ContinuousLinearMap.adjoint (Oinf μ ν β) = Oinf μ ν β') ∧
      (∀ e e' : TF K n, (∀ x, e' x = conj (e x⁻¹)) → ContinuousLinearMap.adjoint (Ofin μ m e) = Ofin μ m e') ∧
      (∀ β : TI K n, ‖Oinf μ ν β‖ ≤ ∫ x, ‖β x‖ ∂ν) ∧ (∀ e : TF K n, ‖Ofin μ m e‖ ≤ ∫ x, ‖e x‖ ∂m) ∧
      (∀ (β : TI K n) (e : TF K n), Commute (Oinf μ ν β) (Ofin μ m e)) ∧
      ∀ (β : TI K n) (h : AdelicGLn.FiniteAdelicGL K n), Commute (Oinf μ ν β) (rhoF μ h) := by
  intro K _ _ n μ _ ν _ m _
  obtain ⟨hν₁, hν₂⟩ := (Tf.unimod K n).1 ν
  obtain ⟨hm₁, hm₂⟩ := (Tf.unimod K n).2 m
  have hpq : ∀ (a : archGroup K n) (b : AdelicGLn.FiniteAdelicGL K n),
      archP K n a * MultiplicityOne.finProj K n b = MultiplicityOne.finProj K n b * archP K n a :=
    fun a b => (MultiplicityOne.finProj_mul_archProj_comm b (a : ArchUnits K n)).symm
  refine ⟨fun β β' => ⟨?_, ?_⟩, fun e e' => ⟨?_, ?_⟩, fun c β e => ⟨?_, ?_⟩, fun β β' h => ?_, fun e e' h => ?_,
    fun β => ?_, fun e => ?_, fun β e => ?_, fun β h => ?_⟩
  · exact CuspidalProjection.integrated_conv ν _ β β'
  · exact int_add _ ν β β'
  · exact CuspidalProjection.integrated_conv m _ e e'
  · exact int_add _ m e e'
  · exact int_smul _ ν c β
  · exact int_smul _ m c e
  · exact (Tf.adjInt _ _ _ ν β β' h).1
  · exact (Tf.adjInt _ _ _ m e e' h).1
  · exact norm_int_le _ ν β
  · exact norm_int_le _ m e
  · exact (Tf.commInt _ _ _ _ (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) (archP K n) continuous_archP
      (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj ν m β e).2 hpq
  · exact int_commute _ (archP K n) continuous_archP ν _ (MultiplicityOne.finProj K n h) fun a => (hpq a h).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem integrable_slice {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (a : archGroup K n) :
    Integrable (fun s => β (a * zInf K n s)) GroundTheory.Global.posRealMeasure := by
  have hc : Continuous fun s : {r : ℝ // 0 < r} => β (a * zInf K n s) :=
    β.continuous.comp (continuous_const.mul continuous_zInf)
  refine hc.integrable_of_hasCompactSupport ?_
  have hD : IsCompact ((fun r : {r : ℝ // 0 < r} => r * (detA K n a)⁻¹) '' (detA K n '' tsupport β)) :=
    (β.hasCompactSupport.isCompact.image continuous_detA).image (continuous_id.mul continuous_const)
  refine HasCompactSupport.intro hD fun s hs => ?_
  by_contra hne
  exact hs ⟨s * detA K n a, mem_of_kernel_ne_zero hn hne, by simp⟩

private theorem kbar_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β β' : TI K n) (a : archGroup K n) : kbar (β + β' : TI K n) a = kbar β a + kbar β' a := by
  simp only [kbar, CompactlySupportedContinuousMap.add_apply]
  exact integral_add (integrable_slice hn β a) (integrable_slice hn β' a)

private theorem kbar_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : ℂ) (β : TI K n) (a : archGroup K n) : kbar (c • β : TI K n) a = c * kbar β a := by
  simp only [kbar, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

private theorem tensFun_support_bound {K : Type} [Field K] [NumberField K] {n : ℕ}
    (hn : 0 < n) (β : TI K n) (e : TF K n) :
    IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      Function.support (tensFun β e) ⊆
        archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e := by
  refine ⟨(β.hasCompactSupport.isCompact.image continuous_archP).mul
    (e.hasCompactSupport.isCompact.image MultiplicityOne.continuous_finProj), ?_⟩
  intro x hx
  let a := infPart K n (x : AdelicGLn.AdelicGL K n)
  let h := finPart K n (x : AdelicGLn.AdelicGL K n)
  change kbar β a * e h ≠ 0 at hx
  have he := right_ne_zero_of_mul hx
  obtain ⟨s, hs⟩ : ∃ s, β (a * zInf K n s) ≠ 0 := by
    by_contra h0
    simp only [not_exists, ne_eq, not_not] at h0
    exact left_ne_zero_of_mul hx (by simp [kbar, h0])
  have hproj : archP K n (a * zInf K n s) * MultiplicityOne.finProj K n h = x := by
    have hf : MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul]
    change retractOne (infEmb K n (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      finEmb K n (finPart K n (x : AdelicGLn.AdelicGL K n))) = x
    rw [infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  rw [← hproj]
  exact Set.mul_mem_mul ⟨_, subset_tsupport _ hs, rfl⟩ ⟨_, subset_tsupport _ he, rfl⟩

private theorem tens_apply' {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (e : TF K n) (x : normOneGL (K := K) (n := n)) : tens β e x = tensFun β e x := by
  have h1 : Continuous (tensFun β e) := by
    unfold tensFun
    exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  obtain ⟨hC, hS⟩ := tensFun_support_bound hn β e
  have h2 : HasCompactSupport (tensFun β e) :=
    hC.of_isClosed_subset isClosed_closure (closure_minimal hS hC.isClosed)
  have h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) := ⟨h1, h2⟩
  rw [tens, dite_eq_left h]
  rfl

theorem UpperTheory.ConvolutionTheory.Tf.tensApply :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n), (∀ x, tens β e x = tensFun β e x) ∧
      (tsupport (tens β e) ⊆ archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      (∀ β', tens (β + β') e = tens β e + tens β' e) ∧ (∀ e', tens β (e + e') = tens β e + tens β e') ∧
      ∀ c : ℂ, tens (c • β) e = c • tens β e ∧ tens β (c • e) = c • tens β e := by
  intro K _ _ n hn β e
  refine ⟨tens_apply' hn β e, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hC, hS⟩ := tensFun_support_bound hn β e
    refine closure_minimal ?_ hC.isClosed
    intro x hx
    apply hS
    rwa [Function.mem_support, ← tens_apply' hn β e x]
  · intro β'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, kbar_add hn, add_mul]
  · intro e'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, mul_add]
  · intro c
    constructor
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, kbar_smul,
        smul_eq_mul, mul_assoc]
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, smul_eq_mul]
      ring
end

