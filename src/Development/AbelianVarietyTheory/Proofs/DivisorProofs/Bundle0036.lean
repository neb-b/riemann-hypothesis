module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvolEqOfFixed
section
namespace GlobalTheory

theorem exists_mul_invol_eq_of_fixed (k : Type) [Field k] [Finite k] (τ : k →+* k)
    (hτ : Function.Involutive τ) (hne : ∃ b : k, τ b ≠ b) (c : k) (hc : τ c = c) :
    ∃ a : k, a * τ a = c := by
  classical
  obtain ⟨b, hb⟩ := hne
  let F : Subfield k := τ.eqLocusField (RingHom.id k)
  have hd : b - τ b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)

  let f : F × F → k := fun p => (p.1 : k) + (p.2 : k) * b
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨α, β⟩ ⟨α', β'⟩ h
      have ea : τ (α : k) = α := α.2
      have eb : τ (β : k) = β := β.2
      have ea' : τ (α' : k) = α' := α'.2
      have eb' : τ (β' : k) = β' := β'.2
      have h0 : (α : k) + β * b = α' + β' * b := h
      have h1 : τ ((α : k) + β * b) = τ ((α' : k) + β' * b) := by rw [h0]
      rw [map_add (f := _), map_mul, map_add (f := _), map_mul, ea, eb, ea', eb'] at h1
      have hβ : (β : k) = β' := by
        have h2 : ((β : k) - β') * (b - τ b) = 0 := by linear_combination h0 - h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hd
      have hα : (α : k) = α' := by
        rw [hβ] at h0
        linear_combination h0
      exact Prod.ext (Subtype.ext hα) (Subtype.ext hβ)
    · intro x
      have hβ : τ ((x - τ x) / (b - τ b)) = (x - τ x) / (b - τ b) := by
        rw [map_div₀, map_sub, map_sub, hτ x, hτ b, ← neg_sub x (τ x), ← neg_sub b (τ b),
          neg_div_neg_eq]
      have hm : (x - τ x) / (b - τ b) * (b - τ b) = x - τ x := div_mul_cancel₀ _ hd
      have hα : τ (x - (x - τ x) / (b - τ b) * b) = x - (x - τ x) / (b - τ b) * b := by
        rw [map_sub, map_mul, hβ]
        linear_combination hm
      refine ⟨(⟨x - (x - τ x) / (b - τ b) * b, hα⟩, ⟨(x - τ x) / (b - τ b), hβ⟩), ?_⟩
      show x - (x - τ x) / (b - τ b) * b + (x - τ x) / (b - τ b) * b = x
      ring
  have hcard : Nat.card k = Nat.card F ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, sq]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hrank : Module.finrank F k = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := k)
    rw [hcard] at h
    exact (Nat.pow_right_injective hq h).symm

  let τ' : k ≃ₐ[F] k := AlgEquiv.ofBijective { τ with commutes' := fun r => r.2 } hτ.bijective
  have hτ' : ∀ x, τ' x = τ x := fun _ => rfl
  have hne1 : (1 : k ≃ₐ[F] k) ≠ τ' := by
    intro h
    apply hb
    rw [← hτ' b, ← h]
    rfl
  have hcardG : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hrank]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, τ'} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcardG, Finset.card_pair hne1]

  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F k ⟨c, hc⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [ha, huniv, Finset.prod_pair hne1] at h
  refine ⟨a, ?_⟩
  calc a * τ a = (1 : k ≃ₐ[F] k) a * τ' a := rfl
    _ = c := h.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemOfForall
section
namespace GlobalTheory.MultipleMembershipForAll

open IsLocalRing

theorem exists_mul_mem_of_forall {S : Type} [CommRing S] (Q I : Ideal S) [hQp : Q.IsPrime]
    (hQ : Q.FG) (h : ∀ x ∈ Q, ∃ g ∉ Q, g * x ∈ I) : ∃ g ∉ Q, ∀ x ∈ Q, g * x ∈ I := by
  classical
  obtain ⟨s, hs⟩ := hQ

  suffices H : ∀ s' : Finset S, (s' : Set S) ⊆ Q →
      ∃ g ∉ Q, ∀ x ∈ Ideal.span (s' : Set S), g * x ∈ I by
    obtain ⟨g, hg, hgI⟩ := H s (by rw [← hs]; exact Submodule.subset_span)
    exact ⟨g, hg, fun x hx => hgI x (by rw [hs]; exact hx)⟩
  intro s'
  induction s' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨1, fun h1 => hQp.ne_top ((Ideal.eq_top_iff_one Q).mpr h1), fun x hx => ?_⟩
    rw [Finset.coe_empty, Ideal.span_empty, Ideal.mem_bot] at hx
    simp [hx]
  | insert a s' ha ih =>
    intro hsub
    rw [Finset.coe_insert] at hsub
    obtain ⟨g, hg, hgI⟩ := ih ((Set.subset_insert _ _).trans hsub)
    obtain ⟨ga, hga, hgaI⟩ := h a (hsub (Set.mem_insert _ _))
    refine ⟨ga * g, fun hm => (hQp.mem_or_mem hm).elim hga hg, fun x hx => ?_⟩
    rw [Finset.coe_insert, Ideal.span_insert, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e1 : ga * g * (r * a + z) = (r * g) * (ga * a) + ga * (g * z) := by ring
    rw [e1]
    exact I.add_mem (I.mul_mem_left _ hgaI) (I.mul_mem_left _ (hgI z hz))

theorem main : ∀ (S : Type) [inst : CommRing S] [IsNoetherianRing S] (Q : Ideal S)
    [inst_2 : Ideal.IsPrime Q], ∃ (h : ℕ) (f : Fin h → S), ∃ g ∉ Q, (∀ (j : Fin h), f j ∈ Q) ∧
    (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
    h = Submodule.spanFinrank (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
    ∀ (a : Fin h → S), ∀ u ∉ Q, u * ∑ j : Fin h, a j * f j ∈ Q ^ (2 : ℕ) →
      ∀ (j : Fin h), a j ∈ Q := by
  intro S _ _ Q _
  classical
  let R := Localization.AtPrime Q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  obtain ⟨t, htcard, htspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank

  have hsurj : ∀ y : R, ∃ p : S × Q.primeCompl, IsLocalization.mk' R p.1 p.2 = y := fun y => by
    obtain ⟨p, hp⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    exact ⟨p, hp⟩
  choose p hxs using hsurj
  let x : R → S := fun y => (p y).1
  let e : Fin t.card → R := fun j => (t.equivFin.symm j : R)
  let f : Fin t.card → S := fun j => x (e j)
  have he : ∀ j, e j ∈ IsLocalRing.maximalIdeal R := fun j => by
    rw [← htspan]; exact Submodule.subset_span (t.equivFin.symm j).2
  have hfQ : ∀ j, f j ∈ Q := fun j => by
    have h := he j
    rw [← hxs (e j)] at h
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff R Q _ _).mp h

  have hspan : Ideal.span (Set.range fun j => algebraMap S R (f j)) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr (hfQ j)
    · rw [← htspan]
      refine Submodule.span_le.mpr fun y hy => ?_
      have hy' : y = e (t.equivFin ⟨y, hy⟩) := by simp [e]
      rw [hy', ← hxs (e _), IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)

  have hloc : ∀ y ∈ Q, ∃ g ∉ Q, g * y ∈ Ideal.span (Set.range f) := by
    intro y hy
    have hmem : algebraMap S R y ∈ (Ideal.span (Set.range f)).map (algebraMap S R) := by
      rw [Ideal.map_span, ← Set.range_comp]
      change algebraMap S R y ∈ Ideal.span (Set.range fun j => algebraMap S R (f j))
      rw [hspan]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr hy
    obtain ⟨g, hg, hgy⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl R _ _).mp hmem
    exact ⟨g, hg, hgy⟩
  obtain ⟨g, hg, hgQ⟩ := exists_mul_mem_of_forall Q _ (IsNoetherian.noetherian Q) hloc
  refine ⟨t.card, f, g, hg, hfQ, hgQ, htcard, ?_⟩

  intro a u hu hsum j0
  by_contra hj0
  set E : Fin t.card → R := fun j => algebraMap S R (f j) with hE
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : IsUnit (algebraMap S R (a j0)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hj0
  have hU : IsUnit (algebraMap S R u) := (IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hu
  have hsq : ∑ j, algebraMap S R (a j) * E j ∈ m ^ 2 := by
    have h1 : algebraMap S R (u * ∑ j, a j * f j) ∈ m ^ 2 := by
      rw [hm, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum] at h1
    obtain ⟨v, hv⟩ := hU.exists_left_inv
    have h2 := Ideal.mul_mem_left _ v h1
    rwa [← mul_assoc, hv, one_mul] at h2
  let N : Ideal R := Ideal.span (((Finset.univ.erase j0).image E : Finset R) : Set R)
  have hEN : ∀ j, j ≠ j0 → E j ∈ N := fun j hj =>
    Ideal.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image_of_mem E (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)))
  have hrest : ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j ∈ N :=
    Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hEN j (Finset.ne_of_mem_erase hj))
  have hj0mem : E j0 ∈ N ⊔ m * m := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => algebraMap S R (a j) * E j)
      (Finset.mem_univ j0)
    have h2 : algebraMap S R (a j0) * E j0 ∈ N ⊔ m * m := by
      have h3 : algebraMap S R (a j0) * E j0 = ∑ j, algebraMap S R (a j) * E j -
          ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j := by
        rw [← hsplit]; ring
      rw [h3]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (by rwa [← sq])) (Ideal.mem_sup_left hrest)
    obtain ⟨v, hv⟩ := hA.exists_left_inv
    have h4 := Ideal.mul_mem_left _ v h2
    rwa [← mul_assoc, hv, one_mul] at h4
  have hle : m ≤ N ⊔ m • m := by
    rw [Ideal.smul_eq_mul]
    calc m = Ideal.span (Set.range E) := hspan.symm
      _ ≤ N ⊔ m * m := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        by_cases hj : j = j0
        · subst hj; exact hj0mem
        · exact Ideal.mem_sup_left (hEN j hj)
  have hmN : m ≤ N := Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  have hNm : N ≤ m := by
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hspan]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hcard : m.spanFinrank ≤ t.card - 1 := by
    calc m.spanFinrank = N.spanFinrank := by rw [le_antisymm hmN hNm]
      _ ≤ (((Finset.univ.erase j0).image E : Finset R) : Set R).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
      _ = ((Finset.univ.erase j0).image E).card := Set.ncard_coe_finset _
      _ ≤ (Finset.univ.erase j0).card := Finset.card_image_le
      _ = t.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hpos : 0 < t.card := j0.pos
  omega

end GlobalTheory.MultipleMembershipForAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIsIntegral
section
namespace GlobalTheory.NatMultipleIntegral

open NumberField

theorem exists_nat_mul_isIntegral (E : Type) [Field E] [NumberField E] (c : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * c) := by
  have h1 : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      rw [Int.cast_neg, neg_neg, Int.cast_natCast]
    rw [this, neg_mul]; exact hint.neg

theorem exists_nat_smul_mem (E : Type) [inst : Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ (q : ℕ), (0 : ℕ) < q ∧ (↑q : E) • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (↑Λ : Set (Fin r → E)) := hΛ ▸ Submodule.mem_top
  have key : ∀ (a : E), IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ := by
    intro a ha x hx
    exact Λ.smul_mem (⟨a, ha⟩ : NumberField.RingOfIntegers E) hx
  have keyn : ∀ (n : ℕ), ∀ x ∈ Λ, (n : E) • x ∈ Λ := by
    intro n x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx n
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨q, hq, hqy⟩ := hy
    refine ⟨p * q, Nat.mul_pos hp hq, ?_⟩
    have e : ((p * q : ℕ) : E) • (x + y) = (q : E) • ((p : E) • x) + (p : E) • ((q : E) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (q : E) (p : E)]
    rw [e]
    exact Λ.add_mem (keyn q _ hpx) (keyn p _ hqy)
  | smul c x _ hx =>
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨n, hn, hint⟩ := exists_nat_mul_isIntegral E c
    refine ⟨n * p, Nat.mul_pos hn hp, ?_⟩
    have e : ((n * p : ℕ) : E) • (c • x) = ((n : E) * c) • ((p : E) • x) := by
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [e]
    exact key _ hint _ hpx

end GlobalTheory.NatMultipleIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimes
section
namespace GlobalTheory.CokerMinimalPrimes

theorem exists_nat_mem_sup (B : Type) [CommRing B] [Module.Finite ℤ B]
    {P Q : Ideal B} (hP : P ∈ minimalPrimes B) (hQ : Q ∈ minimalPrimes B) (hPQ : P ≠ Q) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : B) ∈ P ⊔ Q := by
  have hQm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) Q := hQ
  have hPm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) P := hP
  have hnle : ¬ P ≤ Q := fun h => hPQ (hQm.eq_of_le hPm.1 h)
  haveI : Q.IsPrime := hQm.1.1
  obtain ⟨p, hpP, hpQ⟩ := Set.not_subset.mp hnle
  have hx : Ideal.Quotient.mk Q p ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hxI : Ideal.Quotient.mk Q p ∈ Ideal.map (Ideal.Quotient.mk Q) P :=
    Ideal.mem_map_of_mem _ hpP
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hx hxI
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, eq_intCast, ← map_intCast (Ideal.Quotient.mk Q),
    Ideal.mem_quotient_iff_mem_sup] at hk
  refine ⟨k.natAbs, by simpa using hk0, ?_⟩
  rcases Int.natAbs_eq k with h | h
  · rw [h, Int.cast_natCast] at hk; exact hk
  · rw [h, Int.cast_neg, Int.cast_natCast] at hk; simpa using (P ⊔ Q).neg_mem hk

theorem exists_pow_mul_mem_range {B : Type} [CommRing B] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal B) (m : B) (hm : ∀ i j, i ≠ j → m ∈ I i ⊔ I j)
    (b' : (i : ι) → B ⧸ I i) :
    ∃ a : B, ∀ i, Ideal.Quotient.mk (I i) a
      = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1) * b' i := by

  have hq : ∀ i j, ∃ q : B, i ≠ j → q ∈ I j ∧ m - q ∈ I i := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hm i j hij)
    exact ⟨z, fun _ => ⟨hz, by rw [← hyz]; simpa using hy⟩⟩
  choose q hq using hq
  let e : ι → B := fun i => ∏ j ∈ Finset.univ.erase i, q i j
  have he_mem : ∀ i j, i ≠ j → e i ∈ I j := by
    intro i j hij
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (q i) (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    change ∏ j ∈ Finset.univ.erase i, q i j ∈ I j
    rw [hc]
    exact Ideal.mul_mem_right _ _ (hq i j hij).1
  have he_mod : ∀ i, Ideal.Quotient.mk (I i) (e i)
      = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1) := by
    intro i
    simp only [e, map_prod]
    rw [Finset.prod_congr rfl (g := fun _ => Ideal.Quotient.mk (I i) m), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    exact (Ideal.Quotient.eq.mpr (hq i j hij).2).symm
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I i) (b' i)
  refine ⟨∑ i, e i * c i, fun i => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i]
  · rw [map_mul, he_mod, hc]
  · intro j _ hji
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (he_mem j i hji), zero_mul]
  · intro h; exact (h (Finset.mem_univ i)).elim

theorem exists_nat_mul_mem_range_pi_quotient_minimalPrimes : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧
    ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)),
      (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈
        (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  intro B _ _
  classical
  haveI : IsNoetherian ℤ B := isNoetherian_of_isNoetherianRing_of_finite ℤ B
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  letI : Fintype (minimalPrimes B) := Fintype.ofFinite _
  have hpair : ∀ P Q : minimalPrimes B, ∃ m : ℕ, m ≠ 0 ∧ (P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q) := by
    intro P Q
    by_cases h : P = Q
    · exact ⟨1, one_ne_zero, fun h' => (h' h).elim⟩
    obtain ⟨m, hm0, hm⟩ := exists_nat_mem_sup B P.2 Q.2 (fun e => h (Subtype.ext e))
    exact ⟨m, hm0, fun _ => hm⟩
  choose f hf0 hf using hpair
  let m : ℕ := ∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p.1 p.2
  have hm : ∀ P Q : minimalPrimes B, P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q := by
    intro P Q hPQ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : minimalPrimes B × minimalPrimes B => f p.1 p.2)
      (Finset.mem_univ (P, Q))
    change ((∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2 : ℕ) : B) ∈ _
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hf P Q hPQ)
  refine ⟨m ^ (Fintype.card (minimalPrimes B) - 1), pow_ne_zero _ hm0, fun b' => ?_⟩
  obtain ⟨a, ha⟩ := exists_pow_mul_mem_range (fun P : minimalPrimes B => (P : Ideal B)) (m : B) hm b'
  refine ⟨a, funext fun P => ?_⟩
  change Ideal.Quotient.mk (P : Ideal B) a = _
  rw [ha P, Pi.mul_apply, Pi.natCast_apply, map_natCast]
  push_cast
  rfl

end GlobalTheory.CokerMinimalPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulLe
section
namespace GlobalTheory.NatMultipleIntegralSmulBound

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : RingOfIntegers E, (b : E) = (m : E) * a := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy),
    ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩
  show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a
  rw [smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
  have key : ∀ x ∈ Submodule.span E (↑L' : Set (Fin n → E)), ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨d, hd, hdy⟩ := hy
      refine ⟨c * d, Nat.mul_pos hc hd, ?_⟩
      have e : ((c * d : ℕ) : E) • (x + y) = d • ((c : E) • x) + c • ((d : E) • y) := by
        rw [smul_add, ← Nat.cast_smul_eq_nsmul E d, ← Nat.cast_smul_eq_nsmul E c, smul_smul, smul_smul,
          Nat.cast_mul, mul_comm (d : E)]
      rw [e]
      exact L'.add_mem (L'.nsmul_mem hcx d) (L'.nsmul_mem hdy c)
    | smul e x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨m, hm, b, hb⟩ := exists_nat_mul_integral e
      refine ⟨m * c, Nat.mul_pos hm hc, ?_⟩
      have e' : ((m * c : ℕ) : E) • (e • x) = (b : E) • ((c : E) • x) := by
        rw [hb, smul_smul, smul_smul, Nat.cast_mul]
        congr 1
        ring
      have hb' : (b : E) • ((c : E) • x) = b • ((c : E) • x) := algebraMap_smul E b _
      rw [e', hb']
      exact L'.smul_mem b hcx
  exact key x (h ▸ Submodule.mem_top)

theorem exists_nat_smul_le {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L L' : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) :
    ∃ (c : ℕ), (0 : ℕ) < c ∧ ∀ x ∈ L, (↑c : E) • x ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_nat_smul_mem L' h a
      refine ⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : ((c * d : ℕ) : E) • x = c • ((d : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]
        rw [e]
        exact L'.nsmul_mem hda c
      · have e : ((c * d : ℕ) : E) • x = d • ((c : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]
        rw [e]
        exact L'.nsmul_mem (hcs x hx) d
  obtain ⟨c, hc, hcs⟩ := hs
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact L'.add_mem hx hy
  | smul b x _ hx =>
    rw [Nat.cast_smul_eq_nsmul] at hx ⊢
    rw [smul_comm]
    exact L'.smul_mem b hx

end GlobalTheory.NatMultipleIntegralSmulBound
end

