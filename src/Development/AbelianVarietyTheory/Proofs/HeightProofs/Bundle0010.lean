module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0002
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem exists_natForm_norm_ge {ι J : Type*} [Fintype ι] [DecidableEq ι] (T : Finset J) (n : ℕ)
    (hn : T.card ≤ n) (v : J → ι → ℂ) (ε : ℝ) (hv : ∀ j ∈ T, ∃ a, ε ≤ ‖v j a‖) :
    ∃ c : ι → Fin (n + 1), ∀ j ∈ T, ε / 2 ≤ ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ := by
  classical
  by_contra hcon
  push Not at hcon
  set bad : J → Finset (ι → Fin (n + 1)) := fun j =>
    Finset.univ.filter fun c => ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ < ε / 2 with hbad
  set N := Fintype.card (ι → Fin (n + 1)) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have h1 : ∀ j ∈ T, (bad j).card * (n + 1) ≤ N := by
    intro j hj
    obtain ⟨a, ha⟩ := hv j hj
    have hinj : Set.InjOn (fun p : (ι → Fin (n + 1)) × Fin (n + 1) => Function.update p.1 a p.2)
        ((bad j ×ˢ (Finset.univ : Finset (Fin (n + 1))) : Finset _) : Set _) := by
      rintro ⟨c, k⟩ hc ⟨c', k'⟩ hc' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hbad, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.coe_univ, Set.mem_univ, and_true] at hc hc'
      have hk : k = k' := by simpa using congrFun h a
      have hoff : ∀ b, b ≠ a → c b = c' b := fun b hb => by
        simpa [Function.update_of_ne hb] using congrFun h b
      have hsum : (∑ b, ((c b : ℕ) : ℂ) * v j b) - ∑ b, ((c' b : ℕ) : ℂ) * v j b
          = ((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
        · push_cast; ring
        · intro b _ hb; rw [hoff b hb]; ring
        · simp
      have hlt : ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a‖ < ε := by
        rw [← hsum]
        have := norm_sub_le (∑ b, ((c b : ℕ) : ℂ) * v j b) (∑ b, ((c' b : ℕ) : ℂ) * v j b)
        linarith
      have hca : c a = c' a := by
        by_contra hne
        have hz : (((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) ≠ 0 := by
          intro h0
          apply hne
          apply Fin.ext
          omega
        have h1 : (1 : ℝ) ≤ ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ)‖ := by
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs hz
        rw [norm_mul] at hlt
        nlinarith [norm_nonneg (v j a)]
      refine Prod.ext ?_ hk
      funext b
      by_cases hb : b = a
      · subst hb; exact hca
      · exact hoff b hb
    have := Finset.card_le_card_of_injOn _ (t := Finset.univ) (fun _ _ => by simp) hinj
    simpa [hN] using this
  have h2 : (Finset.univ : Finset (ι → Fin (n + 1))) ⊆ T.biUnion bad := by
    intro c _
    obtain ⟨j, hj, h⟩ := hcon c
    exact Finset.mem_biUnion.2 ⟨j, hj, by simpa [hbad] using h⟩
  have h3 : N ≤ ∑ j ∈ T, (bad j).card := (Finset.card_le_card h2).trans Finset.card_biUnion_le
  have h4 : N * (n + 1) ≤ T.card * N := by
    calc N * (n + 1) ≤ (∑ j ∈ T, (bad j).card) * (n + 1) := Nat.mul_le_mul_right _ h3
      _ = ∑ j ∈ T, (bad j).card * (n + 1) := Finset.sum_mul ..
      _ ≤ ∑ j ∈ T, N := Finset.sum_le_sum h1
      _ = T.card * N := by simp
  nlinarith

theorem exists_root_near_of_norm_eval_lt (p : Polynomial ℂ) (hp : p.Monic) (x : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h : ‖p.eval x‖ < δ ^ p.natDegree) : ∃ r, p.IsRoot r ∧ ‖r - x‖ < δ := by
  by_contra hcon
  push Not at hcon
  have hs := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots_of_monic hp, hs.natDegree_eq_card_roots] at h
  have key : ∀ s : Multiset ℂ, (∀ r ∈ s, δ ≤ ‖r - x‖) →
      δ ^ s.card ≤ ‖(s.map fun r => x - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ']
      refine mul_le_mul ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)) (by positivity)
        (norm_nonneg _)
      rw [norm_sub_rev]
      exact hs a (Multiset.mem_cons_self _ _)
  exact absurd h (not_lt.2 (key _ fun r hr => hcon r (Polynomial.isRoot_of_mem_roots hr)))

theorem exists_embeddings_over_injective (R A Ω : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    [FaithfulSMul R A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] :
    ∃ n : ℕ, ∀ τ : R →+* ℂ, Function.Injective τ → ∃ T : Finset (Ω →+* ℂ), T.card ≤ n ∧
      (∀ σ ∈ T, σ.comp ((algebraMap A Ω).comp (algebraMap R A)) = τ) ∧
      ∀ (b : A) (r : ℂ), ((minpoly R b).map τ).IsRoot r → ∃ σ ∈ T, σ (algebraMap A Ω b) = r := by
  classical
  let _ : Algebra R Ω := ((algebraMap A Ω).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2
    ((IsFractionRing.injective A Ω).comp (FaithfulSMul.algebraMap_injective R A))
  let F := FractionRing R
  let _ : Algebra F Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Ω :=
    inferInstance
  have : FiniteDimensional F Ω := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  refine ⟨Module.finrank F Ω, fun τ hτ => ?_⟩
  let _ : Algebra F ℂ := (IsFractionRing.lift hτ : F →+* ℂ).toAlgebra
  have hF : ∀ x : R, algebraMap F ℂ (algebraMap R F x) = τ x := fun x =>
    IsFractionRing.lift_algebraMap hτ x
  let _ : Fintype (Ω →ₐ[F] ℂ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun ψ : Ω →ₐ[F] ℂ => (ψ : Ω →+* ℂ), ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact card_algHom_le_finrank F Ω ℂ
  · intro σ hσ
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hσ
    ext x
    change ψ (algebraMap R Ω x) = τ x
    rw [IsScalarTower.algebraMap_apply R F Ω, AlgHom.commutes, hF]
  · intro b r hr
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    have h1 : r ∈ (minpoly F (algebraMap A Ω b)).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F Ω hb, Polynomial.aeval_def,
        Polynomial.eval₂_map, show (algebraMap F ℂ).comp (algebraMap R F) = τ from RingHom.ext hF,
        Polynomial.eval₂_eq_eval_map]
      exact hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ] at h1
    obtain ⟨ψ, hψ⟩ := h1
    exact ⟨ψ, Finset.mem_image.2 ⟨ψ, Finset.mem_univ _, rfl⟩, hψ⟩

theorem continuous_eval_map_eval₂Hom {K : Type*} [CommRing K] (sg : K →+* ℂ) {D : ℕ}
    (μ : Polynomial (MvPolynomial (Fin D) K)) (x : ℂ) :
    Continuous fun z : Fin D → ℂ => (μ.map (MvPolynomial.eval₂Hom sg z)).eval x := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.continuous_eval _

theorem generic_points_dense : (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0) → ∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε := by
  intro hgen K A Ω _ _ _ _ _ _ _ _ _ _ _ sg φ hφ S ε hε
  classical
  obtain ⟨D, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin D) K
  let _ : Algebra R A := g.toRingHom.toAlgebra
  have : Module.Finite R A := hfin
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm
  obtain ⟨n, hn⟩ := exists_embeddings_over_injective R A Ω
  let z₀ : Fin D → ℂ := fun i => φ (g (MvPolynomial.X i))
  have hz₀ : MvPolynomial.eval₂Hom sg z₀ = φ.comp (algebraMap R A) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change _ = φ (g (algebraMap K _ k))
      rw [AlgHom.commutes, ← hφ]
      simp
    · intro i
      simp only [MvPolynomial.eval₂Hom_X']
      rfl
  let b : (S → Fin (n + 1)) → A := fun c => ∑ a : S, ((c a : ℕ) : A) * (a : A)
  have hev : ∀ᶠ z in nhds z₀, ∀ c, ‖((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z)).eval
      (φ (b c))‖ < (ε / 2) ^ (minpoly R (b c)).natDegree := by
    rw [Filter.eventually_all]
    intro c
    refine ((continuous_eval_map_eval₂Hom sg (minpoly R (b c)) (φ (b c))).norm.tendsto
      z₀).eventually_lt_const ?_
    have h0 : ((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z₀)).eval (φ (b c)) = 0 := by
      rw [hz₀, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
        minpoly.aeval, map_zero]
    simp only [h0, norm_zero]
    positivity
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨z, hz, hzg⟩ := hgen K sg D z₀ η hη
  have hτ : Function.Injective (MvPolynomial.eval₂Hom sg z) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra h
    exact hzg p h hp
  obtain ⟨T, hT, hover, hroot⟩ := hn _ hτ
  have hsmall := hball (y := z) ((dist_pi_lt_iff hη).2 fun i => by
    rw [dist_eq_norm]; exact hz i)
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_natForm_norm_ge T n hT
    (fun σ (a : S) => σ (algebraMap A Ω a) - φ a) ε (by
      intro σ hσ
      have hP : σ ∈ PT (Ω := Ω) sg := by
        ext k
        have := RingHom.congr_fun (hover σ hσ) (MvPolynomial.C k)
        rw [MvPolynomial.eval₂Hom_C] at this
        rw [← this]
        change σ _ = σ (algebraMap A Ω (g (algebraMap K _ k)))
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      obtain ⟨a, ha, h⟩ := hcon σ hP
      exact ⟨⟨a, ha⟩, h⟩)
  have hmon : (minpoly R (b c)).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  obtain ⟨r, hr, hrε⟩ := exists_root_near_of_norm_eval_lt _
    (hmon.map (MvPolynomial.eval₂Hom sg z)) (φ (b c)) (ε / 2) (by positivity)
    (by rw [hmon.natDegree_map]; exact hsmall c)
  obtain ⟨σ, hσ, rfl⟩ := hroot _ r hr
  refine absurd hrε (not_lt.2 ?_)
  have hc' := hc σ hσ
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [b, map_sum, map_mul, map_natCast, mul_sub, Finset.sum_sub_distrib] using hc'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsLinearIndependentDIffTrdegAdjoinEq
section
namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct


open NumberField in
open scoped TensorProduct in
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem _root_.GlobalTheory.exists_linearIndependent_D_iff_trdeg_adjoin_eq {K Ω κ : Type} [Field K] [CharZero K]
    [Field Ω] [Algebra K Ω] {D : ℕ} (hD : Algebra.trdeg K Ω = D) (x : κ → Ω) :
    (∃ J : Fin D → κ, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) ↔
      Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) = D := by
  constructor
  · rintro ⟨J, hJ⟩
    have hind : AlgebraicIndependent K fun k => x (J k) := _root_.ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence K Ω D (fun k => x (J k)) hJ
    let y : Fin D → IntermediateField.adjoin K (Set.range x) :=
      fun k => ⟨x (J k), IntermediateField.subset_adjoin K _ ⟨J k, rfl⟩⟩
    have hy : AlgebraicIndependent K y :=
      AlgebraicIndependent.of_comp (IntermediateField.adjoin K (Set.range x)).val hind
    apply le_antisymm
    · rw [← hD]
      exact trdeg_le_of_injective _ (IntermediateField.adjoin K (Set.range x)).val.injective
    · simpa using hy.cardinalMk_le_trdeg
  · intro h
    set L := IntermediateField.adjoin K (Set.range x) with hL
    set s : Set L := Subtype.val ⁻¹' Set.range x with hs
    have hmem : ∀ z : L, z ∈ IntermediateField.adjoin K s := by
      intro z
      have hle : L ≤ (IntermediateField.adjoin K s).map L.val := by
        refine IntermediateField.adjoin_le_iff.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩,
          IntermediateField.subset_adjoin K _ ⟨i, rfl⟩, rfl⟩
      obtain ⟨m, hm, hmz⟩ := hle z.2
      rwa [show m = z from Subtype.ext hmz] at hm
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K s) L := ⟨fun z => by
      have hz := isAlgebraic_algebraMap (R := IntermediateField.adjoin K s) (A := L) ⟨z, hmem z⟩
      exact IntermediateField.isAlgebraic_adjoin_iff.mp hz⟩
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := K) (A := L) s
    have hcard : Cardinal.mk t = D := by rw [ht.cardinalMk_eq_trdeg, h]
    obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hcard
    let v : t → Ω := fun z => ((z : L) : Ω)
    have hv : AlgebraicIndependent K v := ht.1.map' (f := L.val) Subtype.val_injective
    haveI : Finite t := Finite.of_equiv _ e.symm
    have hvb : IsTranscendenceBasis K v := by
      refine hv.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
      · rw [hD]; exact Cardinal.natCast_lt_aleph0
      · rw [hD, hcard]
    haveI := hvb.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) Ω :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hv
    have hex : ∀ k : Fin D, ∃ i, x i = (((e.symm k : t) : L) : Ω) := fun k => hts (e.symm k).2
    choose J hJ using hex
    refine ⟨J, ?_⟩
    have hfun : (fun k => KaehlerDifferential.D K Ω (x (J k))) = b ∘ e.symm := by
      funext k
      rw [Function.comp_apply, hb, hJ k]
    rw [hfun]
    exact b.linearIndependent.comp _ e.symm.injective

section Ratios

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

end Ratios

open NumberField in
private theorem sImg_eq_sImage_finSuccEquiv_reindex {Ω : Type} [Field Ω] {D N : ℕ} (j : Fin (N + 1))
    (x : Fin N → Ω) (p : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N) :
    _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j x p = _root_.ReciprocityTheory.MultiplicativeHeights.sImage x (p.1, ((finSuccEquiv' j).trans (finSuccEquiv N).symm) p.2) := by
  rcases p with ⟨a, i⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg _root_.ReciprocityTheory.MultiplicativeHeights.sImage
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · simp only [Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv_symm_none, Fin.cases_zero]
    exact congrArg _ (Fin.insertNth_apply_same i _ _)
  · simp only [Equiv.trans_apply, finSuccEquiv'_succAbove, finSuccEquiv_symm_some, Fin.cases_succ]
    exact congrArg _ (Fin.insertNth_apply_succAbove j _ _ k)


open NumberField in
theorem _root_.GlobalTheory.differentials_iff_trdegD_and_genericSection : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (_𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : _root_.ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → ((∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c) ∧ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → Function.Injective (d.sH c) ∧ FiniteDimensional (d.KT c) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS (Ω c) d.D d.N)) := by
  intro K _ _ ι _ Ω _ _ WT _ A _ _ _ _ _𝒜 d c hfg hD hw
  have hadj : IntermediateField.adjoin K
      (Set.range fun j => _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w j c) (d.w (d.jc c) c)) =
      IntermediateField.adjoin K (Set.range (d.x c)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · show _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w (d.jc c) c) (d.w (d.jc c) c) ∈ _
        rw [_root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq hw (one_smul _ _).symm]
        exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨(d.jc c).succAbove k, rfl⟩
  have htr : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c ↔ Algebra.trdeg K (IntermediateField.adjoin K (Set.range (d.x c))) = d.D := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD
    rw [hadj]
  have key := _root_.GlobalTheory.exists_linearIndependent_D_iff_trdeg_adjoin_eq hD (d.x c)
  refine ⟨key.trans htr.symm, fun hT => ?_⟩
  obtain ⟨hind, hfin⟩ := _root_.ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) hfg hD (key.mpr (htr.mp hT))
  let e := (finSuccEquiv' (d.jc c)).trans (finSuccEquiv d.N).symm
  let σ : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, e p.2)
  have hσ : Function.Bijective σ := ((Equiv.refl (Fin (d.D + 1))).prodCongr e).bijective
  have hcomp : _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg (d.jc c) (d.x c) = _root_.ReciprocityTheory.MultiplicativeHeights.sImage (d.x c) ∘ σ :=
    funext fun p => sImg_eq_sImage_finSuccEquiv_reindex _ _ p
  constructor
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.sH _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom
    rw [hcomp]
    exact hind.comp σ hσ.1
  · have hrange : Set.range (_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg (d.jc c) (d.x c)) = Set.range (_root_.ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) := by
      rw [hcomp, Set.range_comp, hσ.2.range_eq, Set.image_univ]
    have hKT : d.KT c = IntermediateField.adjoin K (Set.range (_root_.ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c))) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.KT
      rw [hrange]
    rw [hKT]
    exact hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMeasurableRootsEnumeration
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem continuous_coeff_prod_X_sub_C {ι : Type} (s : Finset ι) (n : ℕ) :
    Continuous fun r : ι → ℂ => (∏ j ∈ s, (X - C (r j))).coeff n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, coeff_mul]
    refine continuous_finsetSum _ fun p _ => Continuous.mul ?_ (ih _)
    simp only [coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact continuous_apply a
    · exact continuous_const

theorem prod_X_sub_C_eq_X_pow_add_sum {δ : ℕ} (r : Fin δ → ℂ) :
    ∏ j, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C ((∏ j, (X - C (r j))).coeff i) * X ^ (i : ℕ) := by
  have hm : (∏ j, (X - C (r j)) : ℂ[X]).Monic :=
    monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hd : (∏ j, (X - C (r j)) : ℂ[X]).natDegree = δ := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have := hm.as_sum
  rw [hd, Finset.sum_range] at this
  exact this

theorem exists_prod_X_sub_C_eq {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ,
      ∏ j, (X - C (r j)) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  first
  | exact @_root_.GlobalTheory.MonicRootsProduct.exists_roots
  | exact _root_.GlobalTheory.MonicRootsProduct.exists_roots
  | (apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootsProduct.exists_roots <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootsProduct.exists_roots ..)

theorem exists_measurable_roots_enumeration :
    ∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ,
      ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) =
        Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) := by
  intro δ
  let e : ℂ ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (fun _ => not_countable_iff.mpr (inferInstance : Uncountable ℝ)
      Complex.ofReal_injective.countable) (not_countable_iff.mpr inferInstance)
  let S : Set (Fin δ → ℂ) := {r | Monotone (e ∘ r)}
  have hS : MeasurableSet S := by
    have : S = ⋂ i, ⋂ j, ⋂ _ : i ≤ j, {r : Fin δ → ℂ | e (r i) ≤ e (r j)} := by
      ext r
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter, Monotone, Function.comp]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le ?_ ?_
    · exact e.measurable.comp (measurable_pi_apply i)
    · exact e.measurable.comp (measurable_pi_apply j)
  let V : (Fin δ → ℂ) → (Fin δ → ℂ) := fun r i => (∏ j, (X - C (r j))).coeff i
  have hV : Measurable V :=
    (continuous_pi fun i => continuous_coeff_prod_X_sub_C _ _).measurable
  haveI : StandardBorelSpace S := hS.standardBorel
  have hinj : Function.Injective fun x : S => V x := by
    rintro ⟨r, hr⟩ ⟨s, hs⟩ h
    have h1 : (∏ j, (X - C (r j)) : ℂ[X]) = ∏ j, (X - C (s j)) := by
      refine (prod_X_sub_C_eq_X_pow_add_sum r).trans
        (Eq.trans ?_ (prod_X_sub_C_eq_X_pow_add_sum s).symm)
      refine congrArg (X ^ δ + ·) (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (fun a => C a * X ^ (i : ℕ)) (congrFun h i)
    have h2 : Finset.univ.val.map r = Finset.univ.val.map s := by
      rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map r),
        ← roots_multiset_prod_X_sub_C (Finset.univ.val.map s), Multiset.map_map,
        Multiset.map_map]
      exact congrArg roots h1
    have h3 : Finset.univ.val.map (e ∘ r) = Finset.univ.val.map (e ∘ s) := by
      rw [← Multiset.map_map, ← Multiset.map_map, h2]
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h3
    have h4 := List.ofFn_injective
      (h3.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hr) (List.sortedLE_ofFn_iff.mpr hs))
    ext i
    exact e.injective (congrFun h4 i)
  have hemb : MeasurableEmbedding fun x : S => V x :=
    (hV.comp measurable_subtype_coe).measurableEmbedding hinj
  obtain ⟨ρ, hρ, hρV⟩ := hemb.exists_measurable_extend (g := fun x : S => (x : Fin δ → ℂ))
    measurable_subtype_coe fun _ => inferInstance
  refine ⟨ρ, hρ, fun c => ?_⟩
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_eq c
  have hrS : r ∘ Tuple.sort (e ∘ r) ∈ S := Tuple.monotone_sort (e ∘ r)
  have hp : (∏ j, (X - C ((r ∘ Tuple.sort (e ∘ r)) j)) : ℂ[X])
      = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
    rw [← hr]
    exact Equiv.prod_comp (Tuple.sort (e ∘ r)) fun j => X - C (r j)
  have hc : V (r ∘ Tuple.sort (e ∘ r)) = c := by
    funext i
    simp only [V]
    rw [hp, coeff_add, coeff_X_pow, if_neg i.2.ne, zero_add, Polynomial.finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact if_neg fun h => hj (Fin.ext h.symm)
    · simp
  have : ρ c = r ∘ Tuple.sort (e ∘ r) := by
    rw [← hc]
    exact congrFun hρV ⟨_, hrS⟩
  rw [this, hp]

end GlobalTheory
end

