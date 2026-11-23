module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Bridge

open MvPolynomial

noncomputable section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem isRelevant_iff (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsRelevant W ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (R := R) W := Iff.rfl

section Homog

variable [DecidableEq K] [∀ k, Fintype (ι k)]

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  simp only [NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  classical
  set T : Finset (Σ k, ι k) := (Finset.univ : Finset (ι k)).map ⟨Sigma.mk k, sigma_mk_injective⟩
  have h1 : ∑ x ∈ m.support, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_left fun x _ hx => ?_
    rw [Finsupp.notMem_support_iff.mp hx, ite_self]
  have h2 : ∑ x ∈ T, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_right fun x _ hx => ?_
    rw [if_neg]
    rintro rfl
    exact hx (Finset.mem_map.mpr ⟨x.2, Finset.mem_univ _, rfl⟩)
  rw [h1, ← h2, Finset.sum_map]
  simp

theorem isMultiHomog_iff (f : NumbersDVR.MRing ι R) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a := by
  unfold NumbersDVR.IsMultiHomog ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog IsWeightedHomogeneous
  simp only [weight_blockWeight, mem_support_iff, funext_iff]

end Homog

section Ideals

variable [DecidableEq K] [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiHomogIdeal P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := R) P := by
  classical
  constructor
  · intro h
    refine ⟨{g | ∃ f ∈ P, ∃ b, g = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f},
      ?_, le_antisymm ?_ ?_⟩
    · rintro g ⟨f, -, b, rfl⟩
      exact ⟨b, (isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact h f hf b
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hom : (Ideal.span S).IsHomogeneous
        (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
      refine Ideal.homogeneous_span _ S fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (isMultiHomog_iff x a).mpr ha⟩
    exact weightedHomogeneousComponent_mem_of_mem (h := hom) (hp := hf) (m := b)

theorem isMultiProjPrime_iff (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (R := R) P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩

end Ideals

section Cycles

theorem multAt_eq_toNat (J W : Ideal (NumbersDVR.MRing ι R)) [W.IsPrime] :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (R := R) J W = (NumbersDVR.multAt J W).toNat := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.multAt NumbersDVR.multAt
  rw [dite_eq_left ‹W.IsPrime›]

theorem divCycle_eq [Fintype K] [∀ k, Fintype (ι k)] [IsNoetherianRing R]
    (P : Ideal (NumbersDVR.MRing ι R)) (f : NumbersDVR.MRing ι R) (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (R := R) P f W : ℤ) := by
  classical
  unfold NumbersDVR.divCycle ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  simp only [Finsupp.ofSupportFinite_coe, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq,
    ← isRelevant_iff]
  split_ifs with h
  · have : W.IsPrime := h.1.1.1
    rw [multAt_eq_toNat]
  · rfl

end Cycles

end

end GroundTheory.Heights₂.Heights.Bridge
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem PlacesRingQuot.proof : PlacesRingQuot.Statement := by
  intro L _ _ S hS g hg
  classical
  set s := hS.toFinset with hs_def
  have hsS : ∀ w, w ∈ s ↔ w ∈ S := fun w ↦ hS.mem_toFinset
  have hgL : (g : L) ≠ 0 := fun h ↦ hg (Subtype.ext h)

  have hw : ∀ (w : FinitePlace L) (x : L), w x =
      ((WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero w.maximalIdeal)
        (w.maximalIdeal.valuation L x) : NNReal) : ℝ) := by
    intro w x
    rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding']
  have hle : ∀ (w : FinitePlace L) (x y : L),
      w x ≤ w y ↔ w.maximalIdeal.valuation L x ≤ w.maximalIdeal.valuation L y := by
    intro w x y
    rw [hw, hw, NNReal.coe_le_coe,
      (WithZeroMulInt.toNNReal_strictMono
        (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w.maximalIdeal)).le_iff_le]
  have hle1 : ∀ (w : FinitePlace L) (x : L), w x ≤ 1 ↔ w.maximalIdeal.valuation L x ≤ 1 := by
    intro w x
    rw [← map_one w, hle, map_one]

  have hn : ∀ w : FinitePlace L, ∃ n : ℕ,
      w ∈ S → w.maximalIdeal.valuation L g = WithZero.exp (-(n : ℤ)) := by
    intro w
    by_cases hwS : w ∈ S
    · have h0 : w.maximalIdeal.valuation L g ≠ 0 := (Valuation.ne_zero_iff _).2 hgL
      have h1 : WithZero.log (w.maximalIdeal.valuation L g) ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp h0, WithZero.exp_zero]
        exact (hle1 w g).1 (g.2 w hwS)
      refine ⟨(-WithZero.log (w.maximalIdeal.valuation L g)).toNat, fun _ ↦ ?_⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
    · exact ⟨0, fun h ↦ absurd h hwS⟩
  choose n hn using hn

  have key : ∀ z : placesRing S, z ∈ Ideal.span {g} ↔
      ∀ w ∈ S, w.maximalIdeal.valuation L z ≤ w.maximalIdeal.valuation L g := by
    intro z
    constructor
    · intro h w hwS
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 h
      have hr : w.maximalIdeal.valuation L r ≤ 1 := (hle1 w r).1 (r.2 w hwS)
      rw [Subring.coe_mul, map_mul]
      calc w.maximalIdeal.valuation L r * w.maximalIdeal.valuation L g
          ≤ 1 * w.maximalIdeal.valuation L g := mul_le_mul_left hr _
        _ = w.maximalIdeal.valuation L g := one_mul _
    · intro h
      refine Ideal.mem_span_singleton'.2 ⟨⟨z * (g : L)⁻¹, fun w hwS ↦ ?_⟩, Subtype.ext ?_⟩
      · have h0 : w.maximalIdeal.valuation L g ≠ 0 := (Valuation.ne_zero_iff _).2 hgL
        rw [hle1, map_mul, map_inv₀]
        exact (mul_inv_le_iff₀ (zero_lt_iff.2 h0)).2 (by simpa using h w hwS)
      · simp [hgL]

  let ι : 𝓞 L →+* placesRing S := (algebraMap (𝓞 L) L).codRestrict (placesRing S) fun a w _ ↦ by
    rw [← FinitePlace.norm_embedding_eq]
    exact FinitePlace.norm_le_one _ _ a
  have hι : ∀ a : 𝓞 L, ((ι a : placesRing S) : L) = algebraMap (𝓞 L) L a := fun _ ↦ rfl
  have hprime : ∀ w ∈ s, Prime (w.maximalIdeal.asIdeal) := fun w _ ↦ w.maximalIdeal.prime
  have hcop : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → i.maximalIdeal ≠ j.maximalIdeal :=
    fun i _ j _ hij h ↦ hij (FinitePlace.maximalIdeal_injective h)
  have hcop' : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → i.maximalIdeal.asIdeal ≠ j.maximalIdeal.asIdeal :=
    fun i hi j hj hij h ↦ hcop i hi j hj hij (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective h)
  let φ : 𝓞 L →+* placesRing S ⧸ Ideal.span {g} := (Ideal.Quotient.mk _).comp ι

  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    have ha : ∀ w : s, ∃ a : 𝓞 L, w.1.maximalIdeal.valuation L (algebraMap (𝓞 L) L a - x) <
        w.1.maximalIdeal.valuation L g := fun w ↦ by
      have h0 : w.1.maximalIdeal.valuation L g ≠ 0 := (Valuation.ne_zero_iff _).2 hgL
      simpa using IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
        w.1.maximalIdeal ((hle1 w.1 x).1 (x.2 w.1 ((hsS w.1).1 w.2))) (Units.mk0 _ h0)
    choose a ha using ha
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
      (fun w : FinitePlace L ↦ w.maximalIdeal.asIdeal) n hprime hcop' a
    refine ⟨y, ?_⟩
    show Ideal.Quotient.mk _ (ι y) = _
    rw [Ideal.Quotient.eq, key]
    intro w hwS
    have hws : w ∈ s := (hsS w).2 hwS
    have h1 : w.maximalIdeal.valuation L (algebraMap (𝓞 L) L (y - a ⟨w, hws⟩)) ≤
        w.maximalIdeal.valuation L g := by
      rw [hn w hwS, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact hy w hws
    have h2 := (ha ⟨w, hws⟩).le
    have he : ((ι y - x : placesRing S) : L) =
        algebraMap (𝓞 L) L (y - a ⟨w, hws⟩) + (algebraMap (𝓞 L) L (a ⟨w, hws⟩) - x) := by
      simp only [AddSubgroupClass.coe_sub, hι, map_sub]
      ring
    rw [he]
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)

  have hker : RingHom.ker φ = ∏ w ∈ s, w.maximalIdeal.asIdeal ^ n w := by
    rw [← IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod s n (fun w ↦ w.maximalIdeal) hcop]
    ext a
    rw [RingHom.mem_ker, show φ a = Ideal.Quotient.mk _ (ι a) from rfl,
      Ideal.Quotient.eq_zero_iff_mem, key, Submodule.mem_finsetInf]
    refine forall_congr' fun w ↦ ?_
    rw [hsS]
    refine imp_congr_right fun hwS ↦ ?_
    rw [hι, hn w hwS, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have hcard : Nat.card (placesRing S ⧸ Ideal.span {g}) =
      ∏ w ∈ s, Ideal.absNorm w.maximalIdeal.asIdeal ^ n w := by
    rw [← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, hker,
      ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_prod]
    simp only [map_pow]
  rw [hcard, finsum_mem_eq_finite_toFinset_sum _ hS, ← hs_def]
  push_cast
  rw [Real.log_prod fun w _ ↦ pow_ne_zero _ (by
    exact_mod_cast (Nat.zero_lt_of_lt
      (NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal)).ne')]
  refine Finset.sum_congr rfl fun w hws ↦ ?_
  have h0 : WithZero.exp (-(n w : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [Real.log_pow, hw, hn w ((hsS w).1 hws), WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZero.log_exp]
  simp [Real.log_zpow]

end GroundTheory.Heights₂.Heights
end

