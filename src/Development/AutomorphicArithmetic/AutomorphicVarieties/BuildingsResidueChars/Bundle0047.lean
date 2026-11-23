module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicModSubmoduleQdetBlockOfGlRel
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModQuantumDetLeviBlocksOfParabolic
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.QuantumDetLeviBlocks

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Formalism.REAL.Tm]
  split_ifs <;> simp

private def pw (ι V : Type) [AddCommGroup V] [Module ℂ V] :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun f := LinearMap.compLeft f ι
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem algMod_of_ne_zero {M : Type} [AddCommGroup M] [Module ℂ M] (S N : Submodule ℂ M)
    (T : Module.End ℂ M) (P : Polynomial ℂ) (hP : P ≠ 0)
    (h : ∀ x ∈ S, Polynomial.aeval T P x ∈ N) : AlgMod S N T := by
  refine ⟨P * Polynomial.C (P.leadingCoeff)⁻¹, Polynomial.monic_mul_leadingCoeff_inv hP, fun x hx => ?_⟩
  rw [mul_comm, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
  exact N.smul_mem _ (h x hx)

end UpperTheory.V.QuantumDetLeviBlocks

open UpperTheory.V.QuantumDetLeviBlocks in
theorem UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (r s : ℕ) (X : Fin (r + s) → Fin (r + s) → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ W Z S : Submodule ℂ M, S ≤ W → (∀ p q, ∀ x ∈ W, X p q x ∈ W) → (∀ (p : Fin r) (q : Fin s), ∀ x ∈ W, X (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Z) → (∀ u, AlgMod S ⊥ (Formalism.REAL.qdet X u)) → ∀ u, AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd s p) (Fin.castAdd s q)) u) ∧ AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin s => X (Fin.natAdd r p) (Fin.natAdd r q)) u) := by
  intro M _ _ r s U hU W Z S hs hW hZ hc u
  let φ := pw S M
  let X : Fin (r + s) → Fin (r + s) → Module.End ℂ (S → M) := fun p q => φ (U p q)
  have hX : Formalism.REAL.GlRel X := by
    intro a b c d
    have := congrArg φ (hU a b c d)
    split_ifs at this ⊢ <;> simpa [X] using this
  let W' : Submodule ℂ (S → M) := Submodule.pi Set.univ fun _ => W
  let N' : Submodule ℂ (S → M) := ⊥ ⊔ Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin s), ∃ x ∈ W',
    y = X (Fin.castAdd s p) (Fin.natAdd r q) x}
  have hle : N' ≤ Submodule.pi Set.univ fun _ => Z := by
    refine sup_le bot_le (Submodule.span_le.2 ?_)
    rintro _ ⟨p, q, x, hx, rfl⟩ i hi
    exact hZ p q _ (hx i hi)
  obtain ⟨-, h1, h2⟩ := UpperTheory.algebraicModSubmodule_qdet_block_of_glRel (S → M) r s X hX W' ⊥ N'
    (fun p q x hx i hi => hW p q _ (hx i hi))
    (fun p q x hx => by rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact Submodule.zero_mem _)
    rfl (fun i => i.1) (fun i _ => hs i.2) (fun u => by
      obtain ⟨P, hP, h⟩ := hc u
      refine ⟨P, hP.ne_zero, (Submodule.mem_bot ℂ).2 ?_⟩
      funext i
      rw [← map_qdet φ U u, Polynomial.aeval_algHom_apply]
      exact (Submodule.mem_bot ℂ).1 (h i.1 i.2))
  constructor
  · obtain ⟨P, hP, h⟩ := h1 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin r => U (Fin.castAdd s p) (Fin.castAdd s q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
  · obtain ⟨P, hP, h⟩ := h2 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin s => U (Fin.natAdd r p) (Fin.natAdd r q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsZFiniteOfCentreSpan
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.isZFinite_of_centre_span :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : archSmooth K n), Centre (Submodule.span ℂ {φ}) → IsZFinite φ := by
  intro K _ _ n φ hφ
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have key := fun τ => UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span (Module.End ℂ (archSmooth K n)) n (gen D (lam K n) τ)
  choose c hc hq using key
  let s : Set (Module.End ℂ (archSmooth K n)) := Set.range (fun p : ι × Fin n => c p.1 p.2)
  have hcZ : ∀ τ k, c τ k ∈ Zc K n := by
    intro τ k
    have h1 : Submodule.span ℂ (Set.range (Formalism.REAL.qdet (gen D (lam K n) τ))) ≤
        Subalgebra.toSubmodule (Zc K n) := by
      rw [Submodule.span_le]
      rintro x ⟨u, rfl⟩
      exact UpperTheory.qdet_generates_universalEnveloping_centre K n ι D τ u
    exact h1 (hc τ k)
  have hsZ : ∀ x ∈ s, x ∈ Zc K n := by
    rintro x ⟨⟨τ, k⟩, rfl⟩
    exact hcZ τ k
  have hAlg : ∀ T ∈ Zc K n, AlgMod (Submodule.span ℂ {φ}) ⊥ T := by
    intro T hT
    apply UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ (uAction '' (isExpLieAlgebra K n).centerU)
    · rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩
      exact Zc_comm (uAction_mem_Zc hz) (uAction_mem_Zc hw)
    · rintro x ⟨z, hz, rfl⟩
      exact hφ z hz
    · exact hT
  have hfd := UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting _ φ s (Set.finite_range _)
    (fun a ha b hb => Zc_comm (hsZ a ha) (hsZ b hb)) (fun T hT => hAlg T (hsZ T hT))
  have hle : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤ Algebra.adjoin ℂ s := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨τ, u, rfl⟩
    show Formalism.REAL.qdet (gen D (lam K n) τ) u ∈ Algebra.adjoin ℂ s
    rw [hq τ u]
    refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun k hk => Subalgebra.smul_mem _ ?_ _)
    exact Algebra.subset_adjoin ⟨(τ, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
  have hsub : Submodule.span ℂ ((fun z => (uAction z) φ) '' ((isExpLieAlgebra K n).centerU : Set _)) ≤
      Submodule.span ℂ ((fun T : Module.End ℂ (archSmooth K n) => T φ) '' (Algebra.adjoin ℂ s : Set _)) := by
    apply Submodule.span_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨uAction z, hle (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz), rfl⟩
  exact Submodule.finiteDimensional_of_le hsub
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RepsIntegralMemClosedSubmodule
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem inner_eq_setIntegral_of_ae (w v : Lp ℂ 2 (quotientMeasure Γ μ)) {g : G → ℂ}
    (h : ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = g y) :
    inner ℂ w v = ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * g y ∂μ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

private theorem closed_stable [IsFiniteMeasure (quotientMeasure Γ μ)]
    (τ : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))) (hτ : IsClosed (τ : Set (Lp ℂ 2 (quotientMeasure Γ μ))))
    (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G → ℂ)
    (hc : Continuous (fun p : U × G => Ψ p.1 p.2)) (hb : ∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C)
    (hinv : ∀ u, ∀ γ ∈ Γ, ∀ m, Ψ u (γ * m) = Ψ u m)
    (hrep : ∀ u, ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = Ψ u y) :
    ∃ v ∈ τ, ∀ᵐ y ∂μ, (v : RightCosetSpace Γ → ℂ) (mk Γ y) = ∫ u, Ψ u y ∂lam := by
  obtain ⟨C, hC⟩ := hb
  choose v hvτ hvr using hrep
  let Φ : G → ℂ := fun m => ∫ u, Ψ u m ∂lam
  have hΦc : Continuous Φ := by
    refine continuous_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
    · intro m
      exact (hc.comp (by fun_prop : Continuous fun u : U => (u, m))).aestronglyMeasurable
    · intro m
      exact Eventually.of_forall fun u => hC u m
    · exact Eventually.of_forall fun u => hc.comp (by fun_prop : Continuous fun m => (u, m))
  have hΦb : ∀ m, ‖Φ m‖ ≤ C * lam.real univ := fun m =>
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun u => hC u m)
  let f : RightCosetSpace Γ → ℂ := Quotient.lift Φ (by
    rintro a b ⟨γ, rfl⟩
    change Φ ((γ : G) * b) = Φ b
    simp only [Φ, hinv _ _ γ.2])
  have hfc : Continuous f :=
    (isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 hΦc
  have hf2 : MemLp f 2 (quotientMeasure Γ μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable (C * lam.real univ) (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ q
      exact hΦb y)
  have hrepΦ : ∀ᵐ y ∂μ, ((hf2.toLp f : Lp ℂ 2 (quotientMeasure Γ μ)) : RightCosetSpace Γ → ℂ) (mk Γ y) = Φ y := by
    have h := QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk Γ μ) (MemLp.coeFn_toLp hf2)
    filter_upwards [h] with y hy
    rw [hy]
    rfl
  refine ⟨hf2.toLp f, ?_, hrepΦ⟩
  haveI : CompleteSpace τ := hτ.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal τ, Submodule.mem_orthogonal]
  intro w hw
  rw [inner_eq_setIntegral_of_ae Γ μ w _ hrepΦ]
  have hw1 : Integrable (fun y => w (mk Γ y)) (μ.restrict (fundamentalDomain Γ)) := by
    have h1 : Integrable w (quotientMeasure Γ μ) :=
      (Lp.memLp w).integrable (by norm_num)
    exact Integrable.comp_measurable h1 (measurable_mk Γ)
  have hwm : StronglyMeasurable (fun y => w (mk Γ y)) := stronglyMeasurable_lift Γ μ w
  have hint : Integrable (Function.uncurry fun (u : U) (y : G) =>
      conj (w (mk Γ y)) * Ψ u y) (lam.prod (μ.restrict (fundamentalDomain Γ))) := by
    refine Integrable.mono' ((hw1.norm.mul_const C).comp_snd lam) ?_ ?_
    · have h1 : StronglyMeasurable (fun p : U × G => conj (w (mk Γ p.2))) :=
        continuous_star.comp_stronglyMeasurable (hwm.comp_measurable measurable_snd)
      exact h1.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC p.1 p.2) (norm_nonneg _)
  calc ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Φ y ∂μ
      = ∫ y in fundamentalDomain Γ, ∫ u, conj (w (mk Γ y)) * Ψ u y ∂lam ∂μ := by
        simp only [Φ, integral_const_mul]
    _ = ∫ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ ∂lam :=
        (integral_integral_swap hint).symm
    _ = 0 := by
        have h0 : ∀ u, ∫ y in fundamentalDomain Γ, conj (w (mk Γ y)) * Ψ u y ∂μ = 0 := by
          intro u
          rw [← inner_eq_setIntegral_of_ae Γ μ w (v u) (hvr u)]
          exact Submodule.inner_left_of_mem_orthogonal (hvτ u) hw
        simp [h0]

end Gen

theorem UpperTheory.reps_integral_mem_closed_submodule :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)), IsClosed (τ : Set (L2 μ)) →
      ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (lam : Measure U) [IsFiniteMeasure lam] (Ψ : U → G1 K n → ℂ),
        Continuous (fun p : U × G1 K n => Ψ p.1 p.2) → (∃ C : ℝ, ∀ u m, ‖Ψ u m‖ ≤ C) → (∀ u, ∀ γ ∈ Gam K n, ∀ m, Ψ u (γ * m) = Ψ u m) → (∀ u, ∃ v ∈ τ, Reps μ v (Ψ u)) →
        ∃ v ∈ τ, Reps μ v fun m => ∫ u, Ψ u m ∂lam := by
  intro K _ _ n μ _ τ hτ U _ _ _ _ lam _ Ψ hc hb hinv hrep
  haveI : IsFiniteMeasure (quotientMeasure (Gam K n) μ) :=
    isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact closed_stable (Gam K n) μ τ hτ U lam Ψ hc hb hinv hrep
end

