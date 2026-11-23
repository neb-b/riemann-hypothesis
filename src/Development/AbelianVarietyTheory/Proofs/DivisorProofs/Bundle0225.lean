module

public import Mathlib
public import GroundTheory.Brauer.BaseChangeCSA
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0176
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRestrictScalarsField
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QTrace

set_option autoImplicit false in
private lemma trace_restrictScalars_rat {F W : Type} [Field F] [NumberField F] [AddCommGroup W]
    [Module F W] [Module ℚ W] [IsScalarTower ℚ F W] [FiniteDimensional F W] (f : W →ₗ[F] W) :
    LinearMap.trace ℚ W (f.restrictScalars ℚ) = Algebra.trace ℚ F (LinearMap.trace F W f) := by
  classical
  let b := Module.finBasis ℚ F
  let d := Module.finBasis F W
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.trace_eq_matrix_trace ℚ (b.smulTower d), LinearMap.trace_eq_matrix_trace F d,
    Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

set_option autoImplicit false in
private lemma trace_mulLeft_matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin n) (Fin n) ℂ) (LinearMap.mulLeft ℂ M) = n * M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  simp only [Matrix.trace, LinearMap.toMatrix_apply, Matrix.diag, Fintype.sum_prod_type]
  have key : ∀ i j, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr
      (LinearMap.mulLeft ℂ M (Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j))) (i, j) = M i i := by
    intro i j
    rw [Matrix.stdBasis_eq_single]
    simp [Matrix.stdBasis]
  simp only [key]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

set_option autoImplicit false in
private lemma embedding_trace_mulLeft_eq_mul_trace {F A : Type} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] (n : ℕ)
    (hn : Module.finrank F A = n ^ 2) (σ : F →+* ℂ) (φ : A →+* Matrix (Fin n) (Fin n) ℂ)
    (hφ : ∀ x : F, φ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) (c : A) :
    σ (LinearMap.trace F A (LinearMap.mulLeft F c)) = n * (φ c).trace := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  haveI : NeZero n := ⟨hn0⟩
  let φF : A →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    { φ with commutes' := fun x => (hφ x).trans rfl }
  let ι : ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Algebra.ofId ℂ _
  let G : TensorProduct F ℂ A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift ι φF (fun z a => Algebra.commute_algebraMap_left z _)
  let H : TensorProduct F A ℂ →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift φF (ι.restrictScalars F)
      (fun a z => (Algebra.commute_algebraMap_left z _).symm)
  have hH : Function.Injective H := by
    rw [← TwoSidedIdeal.ker_eq_bot]
    by_contra hne
    obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot _ hne
    rw [TwoSidedIdeal.mem_ker] at hmem
    have : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) b = 0 := by
      have h1 : H (1 ⊗ₜ[F] b) = φF 1 * (ι.restrictScalars F) b :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [h1, map_one, one_mul] at hmem
      exact hmem
    exact hb ((algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).injective (this.trans (map_zero _).symm))
  have hGH : ∀ x, G x = H (TensorProduct.comm F ℂ A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.comm_tmul]
      simp only [G, H, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, ι, Algebra.ofId_apply]
      exact Algebra.commutes z _
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  have hG : Function.Injective G := by
    intro x y hxy
    rw [hGH, hGH] at hxy
    exact (TensorProduct.comm F ℂ A).injective (hH hxy)
  have hdim : Module.finrank ℂ (TensorProduct F ℂ A) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [_root_.GroundTheory.Brauer.finrank_baseChange_eq, hn, Module.finrank_matrix]
    simp [sq]
  haveI : FiniteDimensional ℂ (TensorProduct F ℂ A) :=
    Module.finite_of_finrank_pos (by rw [hdim]; simp [Module.finrank_matrix, Nat.pos_of_ne_zero hn0])
  let e : TensorProduct F ℂ A ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearEquiv.ofBijective G.toLinearMap
      ⟨hG, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hG⟩
  have hconj : e.conj ((LinearMap.mulLeft F c).baseChange ℂ) = LinearMap.mulLeft ℂ (φ c) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show G _ = φ c * G x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [LinearMap.baseChange_tmul]
      simp only [G, Algebra.TensorProduct.lift_tmul, ι, Algebra.ofId_apply, LinearMap.mulLeft_apply]
      show algebraMap ℂ _ z * φ (c * a) = φ c * (algebraMap ℂ _ z * φ a)
      rw [map_mul, ← mul_assoc, ← mul_assoc, Algebra.commutes z (φ c)]
    | add x y hx hy => simp [map_add (f := _), hx, hy, mul_add]
  rw [← trace_mulLeft_matrix, ← hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

set_option autoImplicit false in
private lemma trace_pi_comp_proj {N : Type} [AddCommGroup N] [Module ℚ N] [FiniteDimensional ℚ N] (m : ℕ)
    (f : N →ₗ[ℚ] N) :
    LinearMap.trace ℚ (Fin m → N) (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) =
      m * LinearMap.trace ℚ N f := by
  let e := TensorProduct.piScalarRight ℚ ℚ N (Fin m)
  have h : e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) = TensorProduct.map f LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hx : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) (e (x ⊗ₜ y)) = e (f x ⊗ₜ y) := by
      ext i
      simp [e, TensorProduct.piScalarRight_apply]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, hx,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← LinearMap.trace_conj' _ e.symm, h, LinearMap.trace_tensorProduct', LinearMap.trace_id]
  simp [mul_comm]

set_option autoImplicit false in
private lemma trace_and_finrank_of_linearEquiv_pi {A M S : Type} [Ring A] [Algebra ℚ A] [AddCommGroup M]
    [Module A M] [Module ℚ M] [IsScalarTower ℚ A M] [AddCommGroup S] [Module A S] [Module ℚ S]
    [IsScalarTower ℚ A S] [FiniteDimensional ℚ S] (k : ℕ) (e : M ≃ₗ[A] (Fin k → S)) (c : A) :
    LinearMap.trace ℚ M (DistribSMul.toLinearMap ℚ M c) =
        k * LinearMap.trace ℚ S (DistribSMul.toLinearMap ℚ S c) ∧
      Module.finrank ℚ M = k * Module.finrank ℚ S := by
  let e' : M ≃ₗ[ℚ] (Fin k → S) := e.restrictScalars ℚ
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.trace_conj' _ e', ← trace_pi_comp_proj]
    congr 1
    refine LinearMap.ext fun v => funext fun x => ?_
    show e (c • e.symm v) x = c • v x
    rw [map_smul, LinearEquiv.apply_symm_apply]
    rfl
  · rw [e'.finrank_eq, Module.finrank_pi_fintype]
    simp

set_option autoImplicit false in
private lemma trace_mul_finrank_eq_finrank_mul_trace {A M : Type} [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]
    [IsSimpleRing A] [AddCommGroup M] [Module A M] [Module ℚ M] [IsScalarTower ℚ A M]
    [FiniteDimensional ℚ M] (c : A) :
    LinearMap.trace ℚ M (DistribSMul.toLinearMap ℚ M c) * Module.finrank ℚ A =
      Module.finrank ℚ M * LinearMap.trace ℚ A (DistribSMul.toLinearMap ℚ A c) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A
  haveI : IsSemisimpleRing A := (IsSimpleRing.isSemisimpleRing_iff_isArtinianRing (R := A)).mpr inferInstance
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite ℚ A M
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A (A × M)
  have hP : IsIsotypicOfType A (A × M) S := IsSimpleRing.isIsotypic A (A × M) S
  have hA : IsIsotypicOfType A A S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inl A A M) LinearMap.inl_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  have hM : IsIsotypicOfType A M S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inr A A M) LinearMap.inr_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  haveI : FiniteDimensional ℚ S :=
    Module.Finite.of_injective ((S.subtype).restrictScalars ℚ) S.injective_subtype
  obtain ⟨k, ⟨eA⟩⟩ := hA.linearEquiv_fun
  obtain ⟨m, ⟨eM⟩⟩ := hM.linearEquiv_fun
  obtain ⟨hA1, hA2⟩ := trace_and_finrank_of_linearEquiv_pi k eA c
  obtain ⟨hM1, hM2⟩ := trace_and_finrank_of_linearEquiv_pi m eM c
  rw [hA1, hA2, hM1, hM2]
  push_cast
  ring


set_option autoImplicit false in
theorem _root_.GlobalTheory.QTrace.q_trace : ∀ {F A V : Type} [Field F] [NumberField F] [Ring A] [Algebra F A] [FiniteDimensional F A] [Algebra.IsCentral F A]
    [IsSimpleRing A] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (n : ℕ), Module.finrank F A = n ^ 2 →
    ∀ (ρ : A →+* Module.End ℚ V) (ψ : (F →+* ℂ) → (A →+* Matrix (Fin n) (Fin n) ℂ)),
    (∀ σ (x : F), ψ σ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : A,
    ((n * Module.finrank ℚ F : ℕ) : ℂ) * ((LinearMap.trace ℚ V (ρ c) : ℚ) : ℂ) =
      (Module.finrank ℚ V : ℂ) * ∑ σ, Matrix.trace (ψ σ c) := by
  intro F A V _ _ _ _ _ _ _ _ _ _ n hn ρ ψ hψ c
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  letI : Algebra ℚ A := RingHom.toAlgebra' ((algebraMap F A).comp (algebraMap ℚ F))
    (fun q x => Algebra.commutes _ x)
  haveI : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ℚ A := Module.Finite.trans F A
  letI : Module A V := Module.compHom V ρ
  have hρq : ∀ q : ℚ, ρ (algebraMap ℚ A q) = algebraMap ℚ (Module.End ℚ V) q := fun q =>
    congrArg (fun f : ℚ →+* Module.End ℚ V => f q)
      (RingHom.ext_rat (ρ.comp (algebraMap ℚ A)) (algebraMap ℚ (Module.End ℚ V)))
  haveI : IsScalarTower ℚ A V := ⟨fun q a v => by
    show ρ (q • a) v = q • ρ a v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hρq, Module.algebraMap_end_apply]⟩
  have hV : LinearMap.trace ℚ V (DistribSMul.toLinearMap ℚ V c) = LinearMap.trace ℚ V (ρ c) := rfl
  have hA : LinearMap.trace ℚ A (DistribSMul.toLinearMap ℚ A c) =
      Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) := by
    rw [← trace_restrictScalars_rat]
    rfl
  have hsum : (algebraMap ℚ ℂ (Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)))) =
      n * ∑ σ, Matrix.trace (ψ σ c) := by
    rw [trace_eq_sum_embeddings ℂ, Finset.mul_sum]
    refine (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ fun τ => ?_)
    exact embedding_trace_mulLeft_eq_mul_trace n hn _ (ψ _) (hψ _) c
  have hdim : Module.finrank ℚ A = Module.finrank ℚ F * n ^ 2 := by
    rw [← hn, Module.finrank_mul_finrank]
  have key := trace_mul_finrank_eq_finrank_mul_trace (A := A) (M := V) c
  rw [hV, hA, hdim] at key
  have key' := congrArg (fun t : ℚ => (t : ℂ)) key
  simp only [Rat.cast_mul, Rat.cast_natCast] at key'
  have hsum' : ((Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) : ℚ) : ℂ) =
      n * ∑ σ, Matrix.trace (ψ σ c) := hsum
  rw [hsum'] at key'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  apply mul_left_cancel₀ hnC
  push_cast at key' ⊢
  linear_combination key'

end GlobalTheory.QTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFinite
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalBoxIndicator

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {S : Set X} (hcl : IsClopen S) (hco : IsCompact S) :
    Set.indicator S (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  classical
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

theorem indicator_box_translate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F _ _ κ _ B hBo hBO hBcof r
  refine ⟨fun v => ?_, ?_⟩
  · set c : κ → v.adicCompletion F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) with hc
    have hS : {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        = (Homeomorph.subRight c) ⁻¹' (Set.univ.pi fun _ => (B v : Set (v.adicCompletion F))) := by
      ext x
      simp [Set.mem_pi, hc]
    have hBc : IsCompact (B v : Set (v.adicCompletion F)) :=
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).of_isClosed_subset
        (AddSubgroup.isClosed_of_isOpen (B v) (hBo v)) (hBO v)
    have hT : IsClopen (Set.univ.pi fun _ : κ => (B v : Set (v.adicCompletion F))) :=
      ⟨isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (B v) (hBo v),
        isOpen_set_pi Set.finite_univ fun _ _ => hBo v⟩
    rw [hS]
    exact indicator_mem_SB (hT.preimage (Homeomorph.subRight c).continuous)
      ((Homeomorph.subRight c).isCompact_preimage.2 (isCompact_univ_pi fun _ => hBc))
  · have hr : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => (r i).2
    filter_upwards [hr, hBcof] with v hv hBv
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hBv, SetLike.mem_coe]
    constructor
    · intro h
      have := (v.adicCompletionIntegers F).add_mem _ _ h (hv i)
      simpa using this
    · intro h
      exact (v.adicCompletionIntegers F).sub_mem h (hv i)

end GlobalTheory.LocalBoxIndicator

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCharacterInvariantForm
section
open MeasureTheory

namespace GlobalTheory.CharMult

theorem multiplier_symm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  intro V _ _ _ μ hμ T hT m f f' g g' hf' hg'
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨d, A, h, hm⟩ := _root_.GlobalTheory.schwartz_eq_fourier_synthesis V m
  obtain ⟨Φf, hΦf, cΦf, bΦf⟩ := _root_.GlobalTheory.CharFamily.charMul_family V _ A f
  obtain ⟨Φg, hΦg, cΦg, bΦg⟩ := _root_.GlobalTheory.CharFamily.charMul_family V _ (-A) g
  obtain ⟨Λ1, hΛ1⟩ := _root_.GlobalTheory.schwartz_pairing_conj_clm V μ hμ (T g)
  obtain ⟨Λ2, hΛ2⟩ := _root_.GlobalTheory.schwartz_pairing_conj_clm V μ hμ (T f)
  have hint : ∀ (Φ : EuclideanSpace ℝ (Fin d) → SchwartzMap V ℂ), Continuous Φ →
      (∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n)) →
      ∀ (c : EuclideanSpace ℝ (Fin d) → ℂ), (∀ ξ, ‖c ξ‖ = ‖h ξ‖) →
      ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) := by
    intro Φ hΦ hb c hc k n
    obtain ⟨C, hC⟩ := hb k n
    have hcont : Continuous (fun ξ => SchwartzMap.seminorm ℂ k n (Φ ξ)) :=
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)).comp hΦ
    have i1 : Integrable (fun ξ => ‖h ξ‖) := h.integrable.norm
    have i2 : Integrable (fun ξ => ‖ξ‖ ^ n * ‖h ξ‖) := h.integrable_pow_mul volume n
    refine Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_
    · simp_rw [hc]
      exact (h.continuous.norm.mul hcont).aestronglyMeasurable
    · filter_upwards with ξ
      rw [hc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]
      calc ‖h ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ ‖h ξ‖ * (C * (1 + ‖ξ‖ ^ n)) :=
            mul_le_mul_of_nonneg_left (hC ξ) (norm_nonneg _)
        _ = C * (‖h ξ‖ + ‖ξ‖ ^ n * ‖h ξ‖) := by ring

  have hkey : ∀ ξ, Λ1 (T (Φf ξ)) = ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    intro ξ
    rw [hΛ1]
    refine hT (A ξ) f (Φf ξ) (Φg ξ) g (hΦf ξ) (fun x => ?_)
    rw [hΦg, ← mul_assoc, ← Complex.exp_add]
    simp [ContinuousLinearMap.neg_apply]
  have lhs : ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    rw [← hΛ1]
    have := _root_.GlobalTheory.schwartz_clm_integral_comm V (EuclideanSpace ℝ (Fin d)) volume Φf cΦf h h.continuous.aestronglyMeasurable
      (hint Φf cΦf bΦf h (fun _ => rfl)) f' (fun x => by
        rw [hf', hm, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦf]; ring) (Λ1.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]; simp_rw [hkey]
  have rhs : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    have e1 : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = starRingEnd ℂ (Λ2 (T g')) := by
      rw [hΛ2, ← integral_conj]; congr 1; funext x; simp [mul_comm]
    have := _root_.GlobalTheory.schwartz_clm_integral_comm V (EuclideanSpace ℝ (Fin d)) volume Φg cΦg (fun ξ => starRingEnd ℂ (h ξ))
      (Complex.continuous_conj.comp h.continuous).aestronglyMeasurable
      (hint Φg cΦg bΦg _ (fun _ => Complex.norm_conj _)) g' (fun x => by
        rw [hg', hm, ← integral_conj, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦg]
        simp only [map_mul, ContinuousLinearMap.neg_apply, ← Complex.exp_conj]
        simp [Complex.ofReal_neg]; ring) (Λ2.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [e1, this, ← integral_conj]
    congr 1; funext ξ
    rw [map_mul, Complex.conj_conj, hΛ2, ← integral_conj]
    congr 2; funext x; simp [mul_comm]
  rw [lhs, rhs]

end GlobalTheory.CharMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumResidueClassSplitBySign
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem tsum_residue_class_split : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by
  intro N _ r R hs
  classical
  let F : ℤ → ℂ := fun t => if (t : ZMod N) = r then R t else 0
  let g : ℤ → ℤ := fun n => (r.val : ℤ) + n * N
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hg : Function.Injective g := by
    intro a b h
    simp only [g] at h
    exact mul_right_cancel₀ hN (add_left_cancel h)
  have hz : ∀ t ∉ Set.range g, F t = 0 := by
    intro t ht
    simp only [F]
    rw [if_neg]
    intro h
    apply ht
    have h2 : ((t - (r.val : ℤ) : ℤ) : ZMod N) = 0 := by
      push_cast
      rw [h, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
    exact ⟨k, by simp only [g]; linear_combination -hk⟩
  have hFg : F ∘ g = fun n : ℤ => R ((r.val : ℤ) + n * N) := by
    funext n
    simp [F, g]
  have hH : HasSum F (∑' n : ℤ, R ((r.val : ℤ) + n * N)) := by
    rw [← hg.hasSum_iff hz, hFg]
    exact hs.hasSum
  rw [← hH.tsum_eq, tsum_int_eq_zero_add_tsum_pnat hH.summable]
  congr 1
  · congr 1
    · simp only [F, Int.cast_zero, eq_comm]
    · refine tsum_congr fun d => ?_
      simp only [F, Int.cast_natCast]
  · refine tsum_congr fun d => ?_
    simp only [F, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdemStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) → A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  first | exact @GlobalTheory.eOp_comp_self_of_conv_idem | exact GlobalTheory.eOp_comp_self_of_conv_idem | (intros; apply GlobalTheory.eOp_comp_self_of_conv_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperHalfPlaneProductProdImRpowContDiffOn
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem upperHalf_prodImPow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ σ
  apply contDiffOn_prod
  intro τ _
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  have hpos : 0 < (z τ).im := hz τ
  have hL : ContDiff ℝ ∞ (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) := by
    have : (fun w : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => (((w τ).im : ℝ) : ℂ)) =
        (Complex.ofRealCLM.comp (Complex.imCLM.comp (ContinuousLinearMap.proj τ))) := by
      ext w; simp
    rw [this]; exact ContinuousLinearMap.contDiff _
  have hslit : (((z τ).im : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hg : ContDiffAt ℂ ∞ (fun s : ℂ => s ^ (-1 - 2 * σ)) (((z τ).im : ℝ) : ℂ) :=
    (analyticAt_id.cpow analyticAt_const hslit).contDiffAt
  exact (hg.restrict_scalars ℝ).comp z hL.contDiffAt

end GlobalTheory
end

