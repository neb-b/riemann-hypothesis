module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMvPolynomialSubMapMem
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing

theorem gaussRing_isDVR {σ : Type} [Finite σ] (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime]
    (hP : P = Ideal.map MvPolynomial.C (maximalIdeal O₁))
    (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial σ O₁) O₂]
    [IsLocalization.AtPrime O₂ P] : ∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂ := by
  have hd : IsDomain O₂ :=
    IsLocalization.isDomain_of_le_nonZeroDivisors O₂ P.primeCompl_le_nonZeroDivisors
  refine ⟨hd, ?_⟩
  have : IsNoetherianRing O₂ :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (maximalIdeal O₁)
  have hg' : maximalIdeal O₁ = Ideal.span {g} := hg
  have hmax : maximalIdeal O₂ =
      Ideal.span {algebraMap (MvPolynomial σ O₁) O₂ (MvPolynomial.C g)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
    conv_lhs => rw [hP]
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField O₂ := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    intro h
    have h1 := hinj (h.trans (map_zero _).symm)
    have h2 : g = 0 := by simpa using h1
    apply IsDiscreteValuationRing.not_a_field O₁
    rw [hg', h2]; simp
  refine ((IsDiscreteValuationRing.TFAE O₂ hnf).out 1 5).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩

theorem exists_mvPolynomial_sub_map_mem {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal S) (h : ∀ x : S, ∃ a : R, x - φ a ∈ I) (p : MvPolynomial σ S) :
    ∃ q : MvPolynomial σ R,
      p - MvPolynomial.map φ q ∈ Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) I := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha⟩ := h x
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := Ideal.add_mem _ ha hb
    convert this using 1
    rw [map_add (f := _)]; ring
  | mul_X p n hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨a * MvPolynomial.X n, ?_⟩
    have := Ideal.mul_mem_right (MvPolynomial.X n) _ ha
    convert this using 1
    rw [map_mul, MvPolynomial.map_X]; ring

theorem gaussRing_completion :
    ∀ (K : Type) [Field K] [NumberField K] (D N : ℕ) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra (𝓞 K) O₁], Function.Injective (algebraMap (𝓞 K) O₁) → Ideal.map (algebraMap (𝓞 K) O₁) la.asIdeal = IsLocalRing.maximalIdeal O₁ → (∀ x : O₁, ∃ a : 𝓞 K, x - algebraMap (𝓞 K) O₁ a ∈ IsLocalRing.maximalIdeal O₁) → ∀ (P : Ideal (MvPolynomial (TVar D N) O₁)) [P.IsPrime], P = Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O₁) → ∀ (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial (TVar D N) O₁) O₂] [IsLocalization.AtPrime O₂ P], (∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂) ∧ ∃ f : Op D N la →+* O₂, (∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) = algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p)) ∧ f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (Op D N la)) = IsLocalRing.maximalIdeal O₂ ∧ ∀ x : O₂, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal O₂ := by
  intro K _ _ D N la O₁ _ _ _ _ hinj hmap hres P _ hP O₂ _ _ _ _
  obtain ⟨hd, hdvr⟩ := gaussRing_isDVR O₁ P hP O₂
  refine ⟨⟨hd, hdvr⟩, ?_⟩
  have hcomap : (maximalIdeal O₁).comap (algebraMap (𝓞 K) O₁) = la.asIdeal := by
    symm
    apply la.isMaximal.eq_of_le
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [← hmap]; exact Ideal.le_comap_map
  have hmem : ∀ p : OT K D N,
      MvPolynomial.map (algebraMap (𝓞 K) O₁) p ∈ P ↔ p ∈ laT D N la := by
    intro p
    rw [hP, MvPolynomial.mem_map_C_iff]
    refine Iff.trans ?_ (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := p)).symm
    refine forall_congr' fun m => ?_
    rw [MvPolynomial.coeff_map, ← hcomap, Ideal.mem_comap]
  let g : OT K D N →+* O₂ :=
    (algebraMap (MvPolynomial (TVar D N) O₁) O₂).comp (MvPolynomial.map (algebraMap (𝓞 K) O₁))
  have hu : ∀ y : (laT D N la).primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units (M := P.primeCompl) O₂
      ⟨MvPolynomial.map (algebraMap (𝓞 K) O₁) (y : OT K D N), fun h => y.2 ((hmem _).1 h)⟩
  let f : Op D N la →+* O₂ := IsLocalization.lift (M := (laT D N la).primeCompl) hu
  have hf : f.comp (algebraMap (OT K D N) (Op D N la)) = g := IsLocalization.lift_comp hu
  have hf' : ∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) =
      algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p) :=
    fun p => IsLocalization.lift_eq hu p
  have hinj₂ := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  have hginj : Function.Injective g := hinj₂.comp (MvPolynomial.map_injective _ hinj)
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (laT D N la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf'] at h1
    have h2 : p = 0 := hginj (h1.symm.trans (map_zero g).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (Op D N la) s).mul_left_eq_zero.mp h
  have hmax : Ideal.map f (maximalIdeal (Op D N la)) = maximalIdeal O₂ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂, ← Ideal.map_map]
    congr 1
    rw [hP, ← hmap, Ideal.map_map]
    change Ideal.map _ (Ideal.map MvPolynomial.C la.asIdeal) = _
    rw [Ideal.map_map]
    congr 1
    ext a
    simp
  refine ⟨f, hf', ?_, ?_, hmax, ?_⟩
  · haveI := Op_isDVR D N la
    algebraize [f]
    have : Module.IsTorsionFree (Op D N la) O₂ := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      exact hfinj
    unfold RingHom.Flat
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : f a ∈ maximalIdeal O₂ := hmax ▸ Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  · intro x
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    obtain ⟨p₀, hp⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres p
    obtain ⟨s₀, hs⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres
      (s : MvPolynomial (TVar D N) O₁)
    rw [← hP] at hp hs
    have hs₀ : s₀ ∈ (laT D N la).primeCompl := by
      intro h0
      apply s.2
      have := P.add_mem hs ((hmem _).2 h0)
      simpa using this
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Op D N la) ⟨s₀, hs₀⟩
    refine ⟨algebraMap (OT K D N) (Op D N la) p₀ * ↑u⁻¹, ?_⟩
    have hm : ∀ q ∈ P, algebraMap (MvPolynomial (TVar D N) O₁) O₂ q ∈ maximalIdeal O₂ := by
      intro q hq
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
      exact Ideal.mem_map_of_mem _ hq
    have h1 := hm _ hp
    have h2 := hm _ hs
    rw [map_sub, ← hf'] at h1 h2
    simp only at h hu'
    rw [← hu'] at h2
    have h3 : f u * f ↑u⁻¹ = 1 := by rw [← map_mul]; simp
    have h4 := Ideal.mul_mem_right (f ↑u⁻¹) _
      (Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ x h2))
    convert h4 using 1
    rw [map_mul, ← h]
    linear_combination (-x) * h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteNormDiscreteNeZeroOfIsDedekindDomain
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_normDiscrete_ne_zero_of_isDedekindDomain {S L : Type*} [CommRing S]
    [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] (g : L) (hg : g ≠ 0) :
    {w : AddValuation L (WithTop ℤ) |
      IsNormDiscrete w ∧ (∀ s : S, 0 ≤ w (algebraMap S L s)) ∧ w g ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap S L b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective S L (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hg
  have hI : Ideal.span {a * b} ≠ (⊥ : Ideal S) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 hb0
  refine ((Ideal.finite_factors hI).image (ValPl.addv L)).subset ?_
  rintro w ⟨hw, h0, hwg⟩
  let Q : Ideal S :=
    { carrier := {b | 0 < w (algebraMap S L b)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
        exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
  have hz : ∀ s : S, s ∉ Q → w (algebraMap S L s) = 0 := fun s hs =>
    le_antisymm (not_lt.1 (hs : ¬ 0 < w (algebraMap S L s))) (h0 s)
  have hprime : Q.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : S) ∈ Q := htop ▸ Submodule.mem_top
      simp [Q] at h1
    · change 0 < w (algebraMap _ L (a * b)) at hab
      rw [map_mul, AddValuation.map_mul] at hab
      by_contra hno
      rw [not_or] at hno
      rw [hz a hno.1, hz b hno.2, add_zero] at hab
      exact lt_irrefl _ hab
  have hab : a * b ∈ Q := by
    by_contra hno
    have ha := hz a fun h => hno (Q.mul_mem_right _ h)
    have hb := hz b fun h => hno (Q.mul_mem_left _ h)
    have h := w.map_mul (algebraMap S L a / algebraMap S L b) (algebraMap S L b)
    rw [div_mul_cancel₀ _ hb1, ha, hb, add_zero] at h
    exact hwg h.symm
  have hne : Q ≠ ⊥ := fun h => mul_ne_zero ha0 hb0 (by rwa [h, Ideal.mem_bot] at hab)
  refine ⟨⟨Q, hprime, hne⟩, ?_, (ValPl.eq_addv _ w hw h0 (fun s => Iff.rfl)).symm⟩
  exact Ideal.dvd_span_singleton.mpr hab


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem finite_zeros_poles_of_trdeg_one :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω),
      (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t →
      ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) |
        IsNormDiscrete v ∧ IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite := by
  open scoped IntermediateField.algebraAdjoinAdjoin in
  intro F Ω _ _ _ _ t hfg htr ht g hg
  have hind : AlgebraicIndependent F (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis F (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [htr]; simp)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin F ({t} : Set Ω)) Ω := by
    have h := hbasis.isAlgebraic_field
    rwa [Set.range_const] at h
  have : Algebra.EssFiniteType F Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType (IntermediateField.adjoin F ({t} : Set Ω)) Ω := .of_comp F _ _
  have : FiniteDimensional (IntermediateField.adjoin F ({t} : Set Ω)) Ω :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsPrincipalIdealRing (Algebra.adjoin F ({t} : Set Ω)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental F t ht).toRingEquiv.toRingHom
      (Polynomial.algEquivOfTranscendental F t ht).surjective
  have : IsDedekindDomain (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) :=
    integralClosure.isDedekindDomain _ (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  have : IsFractionRing (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  refine (finite_normDiscrete_ne_zero_of_isDedekindDomain
    (S := integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) g hg).subset ?_
  rintro w ⟨hw, hF, hwt, hwg⟩
  refine ⟨hw, fun b => ?_, hwg⟩
  have hA : ∀ x ∈ Algebra.adjoin F ({t} : Set Ω), x ∈ vRing w := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact hwt
    | algebraMap r =>
      by_cases hr : r = 0
      · rw [hr, map_zero]; exact zero_mem _
      · exact (hF r hr).ge
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hb : IsIntegral (Algebra.adjoin F ({t} : Set Ω)) (b : Ω) := b.2
  let : Algebra (Algebra.adjoin F ({t} : Set Ω)) (vRing w) :=
    ((algebraMap (Algebra.adjoin F ({t} : Set Ω)) Ω).codRestrict (vRing w)
      (fun x => hA x x.2)).toAlgebra
  have : IsScalarTower (Algebra.adjoin F ({t} : Set Ω)) (vRing w) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) (b : Ω) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  change 0 ≤ w (b : Ω)
  rw [← hy]
  exact y.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableSumEmbeddingsOverGenericPoint
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory


open Polynomial in
theorem finsum_embeddings_over_eq_sum_roots {F L : Type} [Field F] [Field L] [Algebra F L]
    [Algebra.IsSeparable F L] (pb : PowerBasis F L) (τ : F →+* ℂ) {δ : ℕ} (r : Fin δ → ℂ)
    (hr : ∏ i, (X - C (r i)) = (minpoly F pb.gen).map τ) (g : (L →+* ℂ) → ℝ) (g' : ℂ → ℝ)
    (hg : ∀ P : L →+* ℂ, P.comp (algebraMap F L) = τ → g P = g' (P pb.gen)) :
    ∑ᶠ P ∈ {P : L →+* ℂ | P.comp (algebraMap F L) = τ}, g P = ∑ k, g' (r k) := by
  classical
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hsep : (∏ i, (X - C (r i))).Separable := by
    rw [hr]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)
  have hinj : Function.Injective r := separable_prod_X_sub_C_iff.mp hsep
  let P : Fin δ → (L →+* ℂ) := fun k => (pb.lift (r k) (hroot k)).toRingHom
  have hPgen : ∀ k, P k pb.gen = r k := fun k => pb.lift_gen (r k) (hroot k)
  have hPinj : Function.Injective P := by
    intro k l h
    apply hinj
    rw [← hPgen, ← hPgen, h]
  have hPτ : ∀ k, (P k).comp (algebraMap F L) = τ := by
    intro k
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  have hset : {P : L →+* ℂ | P.comp (algebraMap F L) = τ} = Set.range P := by
    ext Q
    constructor
    · intro hQ
      have hQ' : Q.comp (algebraMap F L) = τ := hQ
      let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
      have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
        rw [aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨k, -, hk⟩ := h0
      refine ⟨k, ?_⟩
      have hk' : Q' pb.gen = r k := by simpa [sub_eq_zero] using hk
      have : pb.lift (r k) (hroot k) = Q' := by
        apply pb.algHom_ext
        rw [pb.lift_gen, hk']
      show (pb.lift (r k) (hroot k)).toRingHom = Q
      rw [this]
    · rintro ⟨k, rfl⟩
      exact hPτ k
  rw [hset, finsum_mem_range hPinj, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg _ (hPτ k), hPgen]

theorem measurable_sum_embeddings_over_generic_point :
    (∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ, ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) = Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) → ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i)) := by
  intro hρ K _ _ σ _ L _ _ _ sg m b Nf hNf
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨ρ, hρm, hρ⟩ := hρ pb.dim
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpm : ∀ p : R, Measurable fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.continuous_eval _).measurable
  have hev : ∀ f, Measurable (ev f) := fun f => (hpm _).div (hpm _)
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : Measurable cf := Measurable.of_eval fun i => hev _
  let G : (σ → ℂ) → ℂ → ℝ := fun t z =>
    Nf fun i => ∑ l : Fin pb.dim, ev (pb.basis.repr (b i) l) t * z ^ (l : ℕ)
  refine ⟨fun t => ∑ k, G t (ρ (cf t) k), ?_, ?_⟩
  · refine Finset.measurable_sum _ fun k _ => hNf.comp (Measurable.of_eval fun i => ?_)
    refine Finset.measurable_sum _ fun l _ => (hev _).mul (Measurable.pow_const ?_ _)
    exact (measurable_pi_apply k).comp (hρm.comp hcf)
  · intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra h
      exact ht p h hp
    let τ : F →+* ℂ := IsFractionRing.lift hinj
    have hτa : ∀ p : R, τ (algebraMap R F p) = MvPolynomial.eval₂ sg t p := fun p =>
      IsFractionRing.lift_algebraMap hinj p
    have hτ : ∀ f, τ f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    have hset : {P : L →+* ℂ | ∀ p : R, P (algebraMap F L (algebraMap R F p)) =
        MvPolynomial.eval₂ sg t p} = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
      ext P
      constructor
      · intro hP
        apply IsFractionRing.ringHom_ext (A := R)
        intro p
        rw [hτa]
        exact hP p
      · intro hP p
        have hP' : P.comp (algebraMap F L) = τ := hP
        rw [← hτa, ← hP']
        rfl
    rw [hset]
    symm
    refine finsum_embeddings_over_eq_sum_roots pb τ (ρ (cf t)) ?_ _ (G t) ?_
    · rw [hρ]
      have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
      conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
        Finset.sum_range]
      simp [cf, hτ]
    · intro P hP
      show Nf _ = Nf _
      congr 1
      funext i
      conv_lhs => rw [← pb.basis.sum_repr (b i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, ← hτ, ← hP]
      rfl

end GlobalTheory
end

