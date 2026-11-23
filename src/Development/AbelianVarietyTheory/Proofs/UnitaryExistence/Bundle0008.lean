module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
    exact @GlobalTheory.AdSplit.exists_adele_equiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem one_ne_zero_fracIdeal (F : Type) [Field F] [NumberField F] :
    (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero

theorem mem_adelicIdeal_one_iff_integral (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v, a v ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h v
    have hv := h v
    unfold GlobalTheory.Idele.localIdeal at hv
    revert hv
    generalize a v = y
    intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hk
      exact HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) r
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [show c • x = (c : v.adicCompletion F) * x from rfl]
      exact mul_mem c.2 hx
  · intro h v
    unfold GlobalTheory.Idele.localIdeal
    rw [← mul_one (a v), show a v * 1 = (⟨a v, h v⟩ : v.adicCompletionIntegers F) •
      (1 : v.adicCompletion F) from rfl]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one _⟩)

private theorem exists_valuation_sub_lt_of_injective (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → F) :
    ∃ w : F, (∀ v ∈ T, v.valuation F (w - c v) ≤ 1) ∧ ∀ v ∉ T, v.valuation F w ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c
  set d : 𝓞 F := (b : 𝓞 F) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨r, hr⟩ := RingHom.mem_rangeS.1 (hb v hv)
      refine ⟨r, ?_⟩
      rw [if_pos hv, hr, Algebra.smul_def]
    · exact ⟨0, by simp [hv]⟩
  choose g hg using hex
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors)
    (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun i => g i)
  have key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d -
      (if v ∈ T then c v else 0)) ≤ 1 := by
    intro v hv
    have h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)
        = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]
    rw [h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_if_neg hd0]
    exact (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
  refine ⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩
  · have h := key v (Finset.mem_union_left _ hv)
    rwa [if_pos hv] at h
  · by_cases hvS : v ∈ S
    · have h := key v hvS
      rwa [if_neg hv, sub_zero] at h
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := fun h =>
        hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
      have hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d)
          (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))
      rw [map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one r

private theorem exists_sub_mem_adicCompletionIntegers' (F : Type) [Field F] [NumberField F]
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ w : F, ∀ v, z v - algebraMap F (FiniteAdeleRing (𝓞 F) F) w v ∈
      v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 z.2
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F,
      z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro v
    have hdense : DenseRange (fun c : F => (c : v.adicCompletion F)) :=
      HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)
    have hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} :=
      (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
    have hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} := by
      show z v - z v ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _
    exact hdense.exists_mem_open hopen ⟨z v, hne⟩
  choose c hc using hc
  obtain ⟨w, hw1, hw2⟩ := exists_valuation_sub_lt_of_injective F hfin.toFinset c
  refine ⟨w, fun v => ?_⟩
  rw [FiniteAdeleRing.algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · have h1 : ((c v : F) : v.adicCompletion F) =
        ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F) := by
      rw [← HeightOneSpectrum.adicCompletion.coe_add, sub_add_cancel]
    have h2 : z v - (w : v.adicCompletion F) =
        (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F) := by
      rw [h1]; ring
    rw [h2]
    refine add_mem (hc v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]
    exact hw1 v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    refine sub_mem hz ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hw2 v hv

theorem exists_eq_algebraMap_add_nsmul (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N)
    (y : FiniteAdeleRing (𝓞 F) F) :
    ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      y = algebraMap F _ x + N • a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨w, hw⟩ := exists_sub_mem_adicCompletionIntegers' F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)
  refine ⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y -
    algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩
  have hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hN', map_one]
  rw [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (-y) * hA

theorem strong_approximation_mod_nat : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  intro F _ _ N hN
  refine ⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F N hN y
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
    intro v
    have hNa : (N • a) v ∈ v.adicCompletionIntegers F := by
      rw [show (N • a) v = N • a v from rfl]
      exact nsmul_mem (ha v) N
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v := rfl
    have h := sub_mem (hy v) hNa
    rw [e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx
  subst hr
  exact ⟨r, a, ha, rfl⟩

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem hilbert90_involution_of_idempotent_unit {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (u d e s : R) (hu : u * σ u = 1) (hd : σ d = -d) (hdu : IsUnit d) (h2 : IsUnit (2 : R))
    (he : e * e = e) (hσe : σ e = e) (hs : u + σ u = 2 * s)
    (hun : IsUnit (e * (1 + s) + (1 - e) * (1 - s))) :
    ∃ x : Rˣ, (x : R) = u * σ x := by
  obtain ⟨d', hd'⟩ := hdu.exists_right_inv
  have h3 : IsUnit (e - (1 - e) * d ^ 2) := by
    refine IsUnit.of_mul_eq_one (e - (1 - e) * d' ^ 2) ?_
    have h : d ^ 2 * d' ^ 2 = 1 := by rw [← mul_pow, hd', one_pow]
    linear_combination (1 + d ^ 2 + d' ^ 2 + d ^ 2 * d' ^ 2) * he + (1 - e) * h
  have hx : σ (e * (1 + u) + (1 - e) * d * (1 - u)) = e * (1 + σ u) - (1 - e) * d * (1 - σ u) := by
    simp only [map_add (f := _), map_mul, map_sub, map_one, hσe, hd]; ring
  have hN : (e * (1 + u) + (1 - e) * d * (1 - u)) * (e * (1 + σ u) - (1 - e) * d * (1 - σ u)) =
      2 * (e * (1 + s) + (1 - e) * (1 - s)) * (e - (1 - e) * d ^ 2) := by
    have hv : σ u = 2 * s - u := by linear_combination hs
    rw [hv] at hu ⊢
    have h1 : e * (1 - e) = 0 := by linear_combination - he
    have h4 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
    generalize 1 - e = f at h1 h4 ⊢
    linear_combination (e * e - f * f * d ^ 2) * hu +
      (d * ((1 - u) * (1 + (2 * s - u)) - (1 + u) * (1 - (2 * s - u))) + 2 * (1 + s) * d ^ 2 - 2 * (1 - s)) * h1
  have hxu : IsUnit (e * (1 + u) + (1 - e) * d * (1 - u)) :=
    isUnit_of_mul_isUnit_left (hN ▸ (h2.mul hun).mul h3)
  refine ⟨hxu.unit, ?_⟩
  rw [IsUnit.unit_spec, hx]
  linear_combination (- e - (1 - e) * d) * hu

theorem aut_eq_one_or_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (g : E ≃ₐ[F] E) : g = 1 ∨ g = c := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  by_contra hg
  push Not at hg
  obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact hg.2 ((hx g hg.1).trans (hx c hc).symm)

theorem hilbert90_adeleRing_tensor_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → ∀ u : AdeleRing (𝓞 F) F ⊗[F] E, u * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c (x : AdeleRing (𝓞 F) F ⊗[F] E) := by
  intro F E _ _ _ _ _ c h2 hc u hu
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcc : ∀ x, c (c x) = x := by
    intro x
    rcases aut_eq_one_or_of_finrank_two c h2 hc (c * c) with h | h
    · simpa using congrArg (fun g : E ≃ₐ[F] E => g x) h
    · exact absurd (by simpa using h) hc
  have htr : ∀ x : E, ∃ t : F, x + c x = algebraMap F E t := by
    intro x
    have : x + c x ∈ Set.range (algebraMap F E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro g
      rcases aut_eq_one_or_of_finrank_two c h2 hc g with rfl | rfl
      · rfl
      · rw [map_add (f := _), hcc, add_comm]
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht.symm⟩
  have hsg : ∀ (a : AdeleRing (𝓞 F) F) (x : E), sg (AdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
    intro a x; simp [sg]
  have hσ : ∀ z, sg (AdeleRing (𝓞 F) F) c (sg (AdeleRing (𝓞 F) F) c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [hsg, hsg, hcc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hT : ∀ z, ∃ t : AdeleRing (𝓞 F) F, z + sg (AdeleRing (𝓞 F) F) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      rw [hsg, ← TensorProduct.tmul_add, ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  obtain ⟨t, ht⟩ := hT u
  obtain ⟨e, he, hun⟩ := _root_.GlobalTheory.AdIdem.exists_idem_isUnit F ((2 : F)⁻¹ • t)
  let ι : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeLeftRingHom
  have hι : ∀ a, ι a = a ⊗ₜ 1 := fun a => rfl
  let κ : E →ₐ[F] AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeRight
  have hκ : ∀ a, κ a = 1 ⊗ₜ a := fun a => rfl
  refine hilbert90_involution_of_idempotent_unit (sg (AdeleRing (𝓞 F) F) c : _ →+* _) hσ u (κ (y - c y)) (ι e)
    (ι ((2 : F)⁻¹ • t)) hu ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change sg _ c _ = _
    rw [← map_neg, hκ, hκ, hsg, map_sub, hcc, neg_sub]
  · exact (IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map κ
  · have := (IsUnit.mk0 (2 : E) two_ne_zero).map κ
    rwa [map_ofNat] at this
  · rw [← map_mul, he]
  · change sg _ c _ = _
    rw [hι, hsg, map_one]
  · change u + sg _ c u = _
    rw [ht, two_mul, ← map_add (f := _), ← add_smul, hι]
    norm_num
  · have := hun.map ι
    simpa only [map_add (f := _), map_mul, map_sub, map_one] using this

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated
section
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.AdLat

variable {F : Type} [Field F] [NumberField F]

theorem valued_natCast_eq (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.intValuation (N : 𝓞 F) := by
  have h : (N : v.adicCompletion F)
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (N : 𝓞 F)) := by simp
  rw [h, ← v.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  rw [valued_natCast_eq]; exact v.intValuation_le_one _

theorem valued_natCast_ne_zero (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    Valued.v (N : v.adicCompletion F) ≠ 0 := by
  rw [valued_natCast_eq]
  exact v.intValuation_ne_zero _ (by exact_mod_cast hN.ne')

theorem exists_nat_valued_pow_le (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, fun n => ?_⟩
  · exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · rw [valued_natCast_eq, HeightOneSpectrum.intValuation_le_pow_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) n

theorem eq_zero_of_valued_le_natCast (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    (h : ∀ N : ℕ, 0 < N → Valued.v y ≤ Valued.v (N : v.adicCompletion F)) : y = 0 := by
  by_contra hy
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (γ := Valued.v y) (by simpa using hy)
  exact absurd ((h _ (pow_pos hp n)).trans (hpn n)) (not_le.2 hn)

theorem exists_limit_of_compatible (v : HeightOneSpectrum (𝓞 F)) (x : ℕ → v.adicCompletion F)
    (h : ∀ N m : ℕ, 0 < N → 0 < m →
      Valued.v (x (N * m) - x N) ≤ Valued.v (N : v.adicCompletion F)) :
    ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
      Valued.v (t - x N) ≤ Valued.v (N : v.adicCompletion F) := by
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit (K := F) v (fun n => x (p ^ n)) (fun m n hnm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add]
    exact (h _ _ (pow_pos hp n) (pow_pos hp k)).trans (hpn n))
  refine ⟨t, fun N hN => ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (valued_natCast_ne_zero v hN)
  have h1 := (ht n).trans hn.le
  have h2 := ((h _ _ (pow_pos hp n) hN).trans (hpn n)).trans hn.le
  have h3 := h _ _ hN (pow_pos hp n)
  have e : t - x N = (t - x (p ^ n)) - (x (p ^ n * N) - x (p ^ n)) + (x (N * p ^ n) - x N) := by
    rw [mul_comm N]; ring
  rw [e]
  exact Valuation.map_add_le _ (Valuation.map_sub_le _ h1 h2) h3

theorem valued_nsmul_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : a v ∈ v.adicCompletionIntegers F) :
    Valued.v ((N • a) v) ≤ Valued.v (N : v.adicCompletion F) := by
  have : (N • a) v = N • a v := rfl
  rw [this, nsmul_eq_mul, map_mul]
  exact mul_le_of_le_one_right' ha

theorem integral_finiteAdele_complete_separated :
    ∀ (F : Type) [Field F] [NumberField F], (∀ y : FiniteAdeleRing (𝓞 F) F, (∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a) → y = 0) ∧ ∀ x : ℕ → FiniteAdeleRing (𝓞 F) F, (∀ N v, x N v ∈ v.adicCompletionIntegers F) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x (N * m) = x N + N • a) → ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = x N + N • a := by
  intro F _ _
  refine ⟨fun y hy => ?_, fun x hx h => ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    refine eq_zero_of_valued_le_natCast v (y v) fun N hN => ?_
    obtain ⟨a, ha, rfl⟩ := hy N hN
    exact valued_nsmul_le v N a (ha v)
  · have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
        Valued.v (t - x N v) ≤ Valued.v (N : v.adicCompletion F) := fun v => by
      refine exists_limit_of_compatible v (fun N => x N v) fun N m hN hm => ?_
      obtain ⟨a, ha, e⟩ := h N m hN hm
      have : x (N * m) v - x N v = (N • a) v := by
        rw [e]
        exact add_sub_cancel_left (x N v) ((N • a) v)
      rw [this]
      exact valued_nsmul_le v N a (ha v)
    choose t ht using key
    have ht1 : ∀ v, t v ∈ v.adicCompletionIntegers F := fun v => by
      have h1 : Valued.v (t v - x 1 v) ≤ 1 := (ht v 1 one_pos).trans (valued_natCast_le_one v 1)
      have h2 : t v - x 1 v ∈ v.adicCompletionIntegers F := h1
      simpa using add_mem h2 (hx 1 v)
    refine ⟨⟨t, Filter.Eventually.of_forall ht1⟩, fun N hN => ?_⟩
    have hq : ∀ v, (t v - x N v) / (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
      fun v => by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ (ht v N hN) zero_le'
    refine ⟨⟨fun v => (t v - x N v) / (N : v.adicCompletion F),
      Filter.Eventually.of_forall hq⟩, hq, ?_⟩
    refine DFunLike.ext _ _ fun v => ?_
    change t v = x N v + N • ((t v - x N v) / (N : v.adicCompletion F))
    have hN0 : (N : v.adicCompletion F) ≠ 0 := fun h0 =>
      valued_natCast_ne_zero v hN (by rw [h0, map_zero])
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hN0]
    ring

end GlobalTheory.AdLat
end
end

