module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem integrated_left {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (h : G)
    (f f' : CompactlySupportedContinuousMap G ℂ) (hf : ∀ g, f' g = f (h⁻¹ * g)) :
    π.integrated μ (UnitaryRep.ccToL1 μ f') = π h ∘L π.integrated μ (UnitaryRep.ccToL1 μ f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.comp_apply, UnitaryRep.inner_map_right, CuspidalProjection.inner_integrated_ccToL1,
    CuspidalProjection.inner_integrated_ccToL1, ← integral_mul_left_eq_self (μ := μ) _ h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  dsimp only
  rw [hf, inv_mul_cancel_left, UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply]

private noncomputable def leftT {K : Type} [Field K] [NumberField K] {n : ℕ} (h : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) : TF K n :=
  ⟨⟨fun g => e (h⁻¹ * g), (map_continuous e).comp (continuous_const.mul continuous_id)⟩,
    e.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft h⁻¹)⟩

private theorem leftT_apply {K : Type} [Field K] [NumberField K] {n : ℕ} (h g : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) :
    leftT h e g = e (h⁻¹ * g) := rfl

private theorem ofin_leftT {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (h : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) :
    Ofin μ m (leftT h e) = rhoF μ h ∘L Ofin μ m e :=
  integrated_left m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n)
      MultiplicityOne.continuous_finProj) h e (leftT h e) (fun g => leftT_apply h g e)

private theorem coset_sum {G L ι : Type*} [Group G] [Group L] [Fintype ι] (loc : L →* G) (p : G → L)
    (hp : ∀ a b, p (a * b) = p a * p b) (h1 : ∀ x, p (loc x) = x)
    (hc : ∀ h, p h = 1 → ∀ x, loc x * h = h * loc x) (J : Subgroup L) (x : L) (U : Subgroup G)
    (hJU : J.map loc ≤ U) (hUJ : ∀ u ∈ U, p u ∈ J) (y : ι → L)
    (inj : Function.Injective (fun i => (QuotientGroup.mk (y i) : L ⧸ J)))
    (rng : Set.range (fun i => (QuotientGroup.mk (y i) : L ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)})
    (c : ℂ) (h : G) :
    ∑ i, (U : Set G).indicator (fun _ => c) ((loc (y i))⁻¹ * h) =
      ((U : Set G) * {loc x} * (U : Set G)).indicator (fun _ => c) h := by
  classical
  have hloc : ∀ j ∈ J, loc j ∈ U := fun j hj => hJU ⟨j, hj, rfl⟩
  have hS : ∀ h, h ∈ (U : Set G) * {loc x} * (U : Set G) ↔ ∃ a ∈ U, ∃ b ∈ U, h = a * loc x * b := by
    intro h
    simp only [Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
  have hmem : ∀ i, ∃ k ∈ J, ∃ j ∈ J, y i = k * x * j := by
    intro i
    have hi : (QuotientGroup.mk (y i) : L ⧸ J) ∈ {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} :=
      rng ▸ ⟨i, rfl⟩
    obtain ⟨k, hk, e⟩ := hi
    exact ⟨k, hk, (k * x)⁻¹ * y i, QuotientGroup.eq.1 e.symm, (mul_inv_cancel_left _ _).symm⟩
  have hA : ∀ i h, (loc (y i))⁻¹ * h ∈ U → h ∈ (U : Set G) * {loc x} * (U : Set G) := by
    intro i h hu
    obtain ⟨k, hk, j, hj, e⟩ := hmem i
    refine (hS h).2 ⟨loc k, hloc k hk, loc j * ((loc (y i))⁻¹ * h), U.mul_mem (hloc j hj) hu, ?_⟩
    rw [e]
    simp only [map_mul]
    group
  have hB : ∀ h ∈ (U : Set G) * {loc x} * (U : Set G), ∃ i, (loc (y i))⁻¹ * h ∈ U := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := (hS h).1 hh
    have hk : p a ∈ J := hUJ a ha
    have ha' : a * (loc (p a))⁻¹ ∈ U := U.mul_mem ha (U.inv_mem (hloc _ hk))
    have hp' : p (a * (loc (p a))⁻¹) = 1 := by
      have e : p ((a * (loc (p a))⁻¹) * loc (p a)) = p a := by rw [inv_mul_cancel_right]
      rw [hp, h1] at e
      exact mul_right_cancel (e.trans (one_mul _).symm)
    have hcm := hc _ hp' (p a * x)
    have hmm : (QuotientGroup.mk (p a * x) : L ⧸ J) ∈ Set.range (fun i => (QuotientGroup.mk (y i) : L ⧸ J)) :=
      rng.symm ▸ ⟨p a, hk, rfl⟩
    obtain ⟨i, hi⟩ := hmm
    have hj : (y i)⁻¹ * (p a * x) ∈ J := QuotientGroup.eq.1 hi
    refine ⟨i, ?_⟩
    have e1 : a * loc x = loc (p a * x) * (a * (loc (p a))⁻¹) := by
      rw [hcm, map_mul]
      group
    have e2 : (loc (y i))⁻¹ * (a * loc x * b) = loc ((y i)⁻¹ * (p a * x)) * (a * (loc (p a))⁻¹) * b := by
      rw [e1, map_mul (f := loc) (y i)⁻¹, map_inv]
      group
    rw [e2]
    exact U.mul_mem (U.mul_mem (hloc _ hj) ha') hb
  have hC : ∀ i i' h, (loc (y i))⁻¹ * h ∈ U → (loc (y i'))⁻¹ * h ∈ U → i = i' := by
    intro i i' h a b
    have hu := U.mul_mem a (U.inv_mem b)
    have e : (loc (y i))⁻¹ * h * ((loc (y i'))⁻¹ * h)⁻¹ = loc ((y i)⁻¹ * y i') := by
      rw [map_mul, map_inv]
      group
    rw [e] at hu
    have hJ := hUJ _ hu
    rw [h1] at hJ
    exact inj (QuotientGroup.eq.2 hJ)
  by_cases hh : h ∈ (U : Set G) * {loc x} * (U : Set G)
  · obtain ⟨i, hi⟩ := hB h hh
    rw [Set.indicator_of_mem hh, Finset.sum_eq_single i
      (fun i' _ hne => Set.indicator_of_notMem (fun hm => hne (hC _ _ _ hm hi)) _) (by simp),
      Set.indicator_of_mem (show _ ∈ (U : Set G) from hi)]
  · rw [Set.indicator_of_notMem hh]
    exact Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun hm => hh (hA i h hm)) _

private theorem cc_sum_apply {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    (f : ι → CompactlySupportedContinuousMap X ℂ) (h : X) : (∑ i ∈ s, f i) h = ∑ i ∈ s, f i h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CompactlySupportedContinuousMap.add_apply, ih]

theorem UpperTheory.ConvolutionTheory.Tf.hopLevel :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
      (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)), IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
      IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
      J.map (AdelicGLn.localEmbedding w) ≤ U → (∀ u ∈ U, finAt w (finEmb K n u) ∈ J) →
      Commute (Hop μ w J x) (prj (fixF μ U)) ∧
      ∃ e : TF K n, (∀ h, e h = ((U : Set (AdelicGLn.FiniteAdelicGL K n)) * {AdelicGLn.localEmbedding w x} * (U : Set (AdelicGLn.FiniteAdelicGL K n))).indicator
          (fun _ => ((m.real U : ℝ) : ℂ)⁻¹) h) ∧ Ofin μ m e = Hop μ w J x ∘L prj (fixF μ U) := by
  intro K _ _ n μ _ m _ w J x U hJo hJc hUo hUc hJU hUJ
  obtain ⟨hfin, hfix, hidem, hsum, hcomm, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJo hJc
  obtain ⟨-, hmemU, hPU, -, -, hmul, -, -, hcommU⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemJ, -, -, hJabs, -, -, -, -⟩ :=
    UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  obtain ⟨-, hl1, -, -, hl5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have hp : ∀ a b, finAt w (finEmb K n (a * b)) = finAt w (finEmb K n a) * finAt w (finEmb K n b) :=
    fun a b => by rw [map_mul, finAt_mul]
  have m1 : ∀ h h', rhoF μ h * rhoF μ h' = rhoF μ (h * h') := fun h h' => (hmul h h').symm
  have hrho : ∀ u ∈ U, Commute (Hop μ w J x) (rhoF μ u) := by
    intro u hu
    have hj : finAt w (finEmb K n u) ∈ J := hUJ u hu
    obtain ⟨j, hjj⟩ : ∃ j, j = finAt w (finEmb K n u) := ⟨_, rfl⟩
    rw [← hjj] at hj
    have hb1 : finAt w (finEmb K n (u * (AdelicGLn.localEmbedding w j)⁻¹)) = 1 := by
      have e : finAt w (finEmb K n ((u * (AdelicGLn.localEmbedding w j)⁻¹) * AdelicGLn.localEmbedding w j)) =
          finAt w (finEmb K n u) := by rw [inv_mul_cancel_right]
      rw [hp, hl1, ← hjj] at e
      exact mul_right_cancel (e.trans (one_mul _).symm)
    have hA : Commute (Hop μ w J x) (rhoF μ (u * (AdelicGLn.localEmbedding w j)⁻¹)) := by
      refine (hcomm _ fun g => ?_).symm
      have hg := hl5 _ hb1 g
      show rhoF μ _ * rhoF μ _ = rhoF μ _ * rhoF μ _
      rw [m1, m1, hg]
    have hB : Commute (Hop μ w J x) (rhoF μ (AdelicGLn.localEmbedding w j)) := by
      have e1 : rhoF μ (AdelicGLn.localEmbedding w j) * Hop μ w J x = Hop μ w J x :=
        ContinuousLinearMap.ext fun v => (hmemJ _).1 (hfix v) _ ⟨j, hj, rfl⟩
      have e2 : Hop μ w J x * rhoF μ (AdelicGLn.localEmbedding w j) = Hop μ w J x := by
        have h3 : prj (fixL μ w J) ∘L rhoF μ (AdelicGLn.localEmbedding w j) = prj (fixL μ w J) :=
          (hJabs _ ⟨j, hj, rfl⟩).2
        calc Hop μ w J x * rhoF μ (AdelicGLn.localEmbedding w j)
            = (Hop μ w J x ∘L prj (fixL μ w J)) ∘L rhoF μ (AdelicGLn.localEmbedding w j) := by rw [hidem]; rfl
          _ = Hop μ w J x ∘L (prj (fixL μ w J) ∘L rhoF μ (AdelicGLn.localEmbedding w j)) := rfl
          _ = Hop μ w J x := by rw [h3, hidem]
      exact e2.trans e1.symm
    have hAB := hA.mul_right hB
    rwa [m1, inv_mul_cancel_right] at hAB
  refine ⟨hcommU _ hrho, ?_⟩
  classical
  obtain ⟨e0, he0, hO⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m U hUo hUc
  haveI : Fintype {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} := hfin.fintype
  obtain ⟨y, hy⟩ : ∃ y : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} → GL (Fin n) (w.adicCompletion K),
      ∀ i, (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J) = i :=
    ⟨fun c => (c : GL (Fin n) (w.adicCompletion K) ⧸ J).out, fun c => QuotientGroup.out_eq' _⟩
  have inj : Function.Injective (fun i => (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) := by
    intro a b hab
    simp only [hy] at hab
    exact Subtype.ext hab
  have rng : Set.range (fun i => (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) =
      {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} := by
    ext c
    constructor
    · rintro ⟨i, rfl⟩
      simp only [hy]
      exact i.2
    · intro hc
      exact ⟨⟨c, hc⟩, hy _⟩
  obtain ⟨-, hadd, -⟩ := UpperTheory.ConvolutionTheory.Tf.opAlg K n μ (Measure.haar : Measure (archGroup K n)) m
  refine ⟨∑ i, leftT (AdelicGLn.localEmbedding w (y i)) e0, fun h => ?_, ?_⟩
  · rw [cc_sum_apply]
    simp only [leftT_apply, he0]
    exact coset_sum (AdelicGLn.localEmbedding w) (fun g => finAt w (finEmb K n g)) hp hl1 hl5 J x U hJU hUJ y inj rng _ h
  · have hs : Ofin μ m (∑ i, leftT (AdelicGLn.localEmbedding w (y i)) e0) =
        ∑ i, Ofin μ m (leftT (AdelicGLn.localEmbedding w (y i)) e0) :=
      map_sum (AddMonoidHom.mk' (Ofin μ m) fun a b => (hadd a b).2) _ _
    rw [hs]
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : prj (fixF μ U) v ∈ fixL μ w J :=
      (hmemJ _).2 fun u hu => (hmemU _).1 (hPU v) u (hJU hu)
    rw [ContinuousLinearMap.comp_apply, hsum _ y inj rng _ hv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofin_leftT, hO]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

attribute [-instance] GlobalTheory.SplitFlip.t2Space_general_linear_group GlobalTheory.SplitFlip.secondCountable_GL in
theorem UpperTheory.ConvolutionTheory.Tf.innerOps :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure],
      (∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n), (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → Oinf μ ν β ∘L prj V = prj V ∘L Oinf μ ν β)) ∧
      (∀ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (e : TF K n), (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → Ofin μ m e ∘L prj V = prj V ∘L Ofin μ m e)) ∧
      (∀ f : TG K n, (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → RR μ f ∘L prj V = prj V ∘L RR μ f)) ∧
      (∀ h, (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → rhoF μ h ∘L prj V = prj V ∘L rhoF μ h)) ∧ (∀ U, (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → prj (fixF μ U) ∘L prj V = prj V ∘L prj (fixF μ U))) ∧
      ∀ (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)), IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
        (∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → Hop μ w J x ∘L prj V = prj V ∘L Hop μ w J x) := by
  intro K _ _ n μ _
  have hI : ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) →
      (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V →
      ∀ g, Commute (prj V) (rightRegularRep (rationalGLOne (K := K) (n := n)) μ g) := by
    intro V hc hi g
    have hi' : (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V.topologicalClosure := by
      rw [hc.submodule_topologicalClosure_eq]; exact hi
    exact ((UnitaryRep.isInvariant_iff_commute_starProjection V.topologicalClosure).mp hi' g).symm
  have hF : ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) →
      (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).IsInvariant V → ∀ h, Commute (prj V) (rhoF μ h) :=
    fun V hc hi h => hI V hc hi _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν _ β V hc hi
    have hT : prj V ∈ ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (archP K n) continuous_archP).intertwiners
        ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (archP K n) continuous_archP) :=
      fun g v => congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hI V hc hi (archP K n g)).eq
    exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ ν hT (UnitaryRep.ccToL1 ν β)).symm
  · intro m _ e V hc hi
    have hT : prj V ∈ ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n)
          MultiplicityOne.continuous_finProj).intertwiners
        ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n)
          MultiplicityOne.continuous_finProj) :=
      fun g v => congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hI V hc hi (MultiplicityOne.finProj K n g)).eq
    exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ m hT (UnitaryRep.ccToL1 m e)).symm
  · intro f V hc hi
    have hT : prj V ∈ (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).intertwiners
        (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) :=
      UnitaryRep.mem_intertwiners_self_iff.mpr (hI V hc hi)
    exact (UnitaryRep.comp_integrated_of_mem_intertwiners _ μ hT (UnitaryRep.ccToL1 μ f)).symm
  · intro h V hc hi
    exact (hF V hc hi h).eq.symm
  · intro U V hc hi
    exact ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.2.2.2.2.2.2.2 (prj V) fun u _ => hF V hc hi u).eq.symm
  · intro w J x ho hk V hc hi
    exact ((UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x ho hk).2.2.2.2.1 (prj V)
      fun g => hF V hc hi _).eq.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem finprod_fib {A B M : Type*} [CommMonoid M] (π : A → B) (p : A → B → Prop)
    (hp : ∀ a b, p a b ↔ π a = b) (f : A → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ b : B, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ᶠ a : A, f a := by
  classical
  have hG : ∀ b, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ a ∈ hf.toFinset with π a = b, f a := by
    intro b
    rw [finprod_subtype_eq_finprod_cond]
    refine finprod_cond_eq_prod_of_cond_iff _ fun {x} hx => ?_
    simp [hp, Function.mem_mulSupport, hx]
  simp_rw [hG]
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf subset_rfl]
  rw [finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset.image π)]
  · exact Finset.prod_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) f
  · intro b hb
    by_contra hb'
    refine hb ?_
    refine Finset.prod_eq_one fun x hx => ?_
    exfalso
    rw [Finset.mem_filter] at hx
    exact hb' (by simpa using ⟨x, by simpa using hx.1, hx.2⟩)

theorem UpperTheory.ConvolutionTheory.Tf.tensEProd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
      (∀ᶠ w : Pl E in Filter.cofinite, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator 1) →
      ∀ g : AdelicGLn.AdelicGL E n,
        ∏ᶠ v : Pl F, GM.prodFn (v := v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = ∏ᶠ w : Pl E, h w (finAt w g) := by
  intro F E _ _ _ _ _ n h hh g
  have hS : (Function.mulSupport fun w : Pl E => h w (finAt w g)).Finite := by
    have hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w g) = 1 := by
      filter_upwards [hh, AdelicGLn.eventually_mem_integralGL E n g] with w h1 h2
      rw [h1, Set.indicator_of_mem (by exact h2)]
      rfl
    exact Filter.eventually_cofinite.1 hev
  have e : ∀ v : Pl F, GM.prodFn (v := v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g)
      = ∏ᶠ w : {w : Pl E // w.asIdeal.LiesOver v.asIdeal}, h w.1 (finAt w.1 g) := by
    intro v
    refine finprod_congr fun w => ?_
    have : GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = finAt w.1 g := by
      ext i j
      rfl
    rw [this]
  simp_rw [e]
  refine finprod_fib (fun w : Pl E => w.under (𝓞 F)) (fun w v => w.asIdeal.LiesOver v.asIdeal) ?_ _ hS
  intro w v
  constructor
  · intro hl
    ext1
    exact (hl.over).symm
  · rintro rfl
    exact ⟨rfl⟩
end

