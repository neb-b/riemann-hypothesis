module

public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0004
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRTypeCountExact
section
open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


set_option maxHeartbeats 800000 in
theorem type_count_exact : TypeCountExact := by
  classical
  intro K _ _ N n hN
  suffices H : ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
      ∏ d ∈ Finset.Icc 1 N,
        (((Finset.univ : Finset (Fin d → K)).filter
          (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d) by
    convert H
  have L1 : ∀ m : Multiset K[X], (∀ q ∈ m, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0) →
      m.prod.Monic ∧ normalizedFactors m.prod = m ∧
        m.prod.natDegree = (m.map Polynomial.natDegree).sum ∧ m.prod.coeff 0 ≠ 0 := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro h
      have ha := h a (by simp)
      obtain ⟨h1, h2, h3, h4⟩ := ih (fun q hq => h q (by simp [hq]))
      have hna : normalize a = a := by
        first
          | exact ha.1.normalize_eq_self
          | exact Polynomial.Monic.normalize_eq_self ha.1
          | simp [normalize_apply, Polynomial.coe_normUnit, ha.1.leadingCoeff]
      rw [Multiset.prod_cons]
      refine ⟨ha.1.mul h1, ?_, ?_, ?_⟩
      · rw [normalizedFactors_mul ha.2.1.ne_zero h1.ne_zero, normalizedFactors_irreducible ha.2.1,
          hna, h2, Multiset.singleton_add]
      · rw [ha.1.natDegree_mul h1, h3, Multiset.map_cons, Multiset.sum_cons]
      · rw [Polynomial.mul_coeff_zero]
        exact mul_ne_zero ha.2.2 h4
  have L2 : ∀ (T : Finset K[X]) (d : ℕ), (T.val.map Polynomial.natDegree).count d =
      (T.filter (fun q => q.natDegree = d)).card := by
    intro T d
    rw [Multiset.count_map]
    exact congrArg Multiset.card (Multiset.filter_congr (fun x _ => eq_comm))
  have F : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 → ∀ q ∈ normalizedFactors (monicOf c),
      q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧ 1 ≤ q.natDegree ∧ q.natDegree ≤ N := by
    intro c hc q hq
    have hirr : Irreducible q := by
      first
        | exact irreducible_of_normalized_factor q hq
        | exact UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hq0 : q ≠ 0 := hirr.ne_zero
    have hnq : normalize q = q := by
      first
        | exact normalize_normalized_factor q hq
        | exact UniqueFactorizationMonoid.normalize_normalized_factor q hq
    have hmon : q.Monic := by
      have h := Polynomial.monic_normalize hq0
      rwa [hnq] at h
    have hdvd : q ∣ monicOf c := by
      first
        | exact dvd_of_mem_normalizedFactors hq
        | exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
    have hp0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
    refine ⟨hmon, hirr, ?_, ?_, ?_⟩
    · intro h0
      apply hc
      exact Polynomial.X_dvd_iff.mp ((Polynomial.X_dvd_iff.mpr h0).trans hdvd)
    · by_contra hlt
      have hz : q.natDegree = 0 := by omega
      have h1 : q = 1 := by
        first
          | exact hmon.natDegree_eq_zero_iff_eq_one.mp hz
          | exact Polynomial.eq_one_of_monic_natDegree_zero hmon hz
      apply hirr.not_isUnit
      rw [h1]
      exact isUnit_one
    · have h := Polynomial.natDegree_le_of_dvd hdvd hp0
      rwa [monicOf_natDegree] at h
  have P : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 →
      (normalizedFactors (monicOf c)).prod = monicOf c := by
    intro c hc
    have hp0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
    have hm := (L1 _ (fun q hq => ⟨(F c hc q hq).1, (F c hc q hq).2.1, (F c hc q hq).2.2.1⟩)).1
    apply Polynomial.eq_of_monic_of_associated hm (monicOf_monic c)
    first
      | exact prod_normalizedFactors hp0
      | exact normalizedFactors_prod hp0
      | exact UniqueFactorizationMonoid.prod_normalizedFactors hp0
      | exact UniqueFactorizationMonoid.normalizedFactors_prod hp0
  set Irr : ℕ → Finset K[X] := fun d => ((Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).image monicOf with hIrrdef
  have hIrr : ∀ (d : ℕ) (q : K[X]), q ∈ Irr d ↔
      q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
    intro d q
    simp only [Irr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨monicOf_monic c, monicOf_natDegree c, h1, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i => q.coeff i, ?_, monicOf_coeffs h1 h2⟩
      rw [monicOf_coeffs h1 h2]
      exact ⟨h3, h4⟩
  set U : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) → Finset K[X] :=
    fun f => (Finset.Icc 1 N).attach.biUnion (fun x => f x.1 x.2) with hUdef
  have hmemT : ∀ (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (q : K[X]),
      q ∈ U f ↔ ∃ d, ∃ hd : d ∈ Finset.Icc 1 N, q ∈ f d hd := by
    intro f q
    simp only [U]
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨x.1, x.2, hx⟩
    · rintro ⟨d, hd, hq⟩
      exact ⟨⟨d, hd⟩, Finset.mem_attach _ _, hq⟩
  have key : ∀ f : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]),
      (∀ d (hd : d ∈ Finset.Icc 1 N), f d hd ∈ (Irr d).powersetCard (n d)) →
      (U f).val.prod.Monic ∧ normalizedFactors (U f).val.prod = (U f).val ∧
        (U f).val.prod.natDegree = N ∧ (U f).val.prod.coeff 0 ≠ 0 ∧
        ∀ d (hd : d ∈ Finset.Icc 1 N), (U f).filter (fun q => q.natDegree = d) = f d hd := by
    intro f hf
    have hprop : ∀ d (hd : d ∈ Finset.Icc 1 N) q, q ∈ f d hd →
        q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := fun d hd q hq =>
      (hIrr d q).mp ((Finset.mem_powersetCard.mp (hf d hd)).1 hq)
    have hfib : ∀ d (hd : d ∈ Finset.Icc 1 N),
        (U f).filter (fun q => q.natDegree = d) = f d hd := by
      intro d hd
      ext q
      rw [Finset.mem_filter, hmemT]
      constructor
      · rintro ⟨⟨d', hd', hq⟩, hdeg⟩
        have hdd : d' = d := (hprop d' hd' q hq).2.1.symm.trans hdeg
        subst hdd
        exact hq
      · intro hq
        exact ⟨⟨d, hd, hq⟩, (hprop d hd q hq).2.1⟩
    have hall : ∀ q ∈ (U f).val, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      obtain ⟨h1, _, h3, h4⟩ := hprop d hd q hq'
      exact ⟨h1, h3, h4⟩
    obtain ⟨hmon, hnf, hdeg, hc0⟩ := L1 _ hall
    refine ⟨hmon, hnf, ?_, hc0, hfib⟩
    rw [hdeg, ← hN]
    have hmaps : ∀ q ∈ U f, q.natDegree ∈ Finset.Icc 1 N := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      rw [(hprop d hd q hq').2.1]
      exact hd
    have hsum : ((U f).val.map Polynomial.natDegree).sum = ∑ q ∈ U f, q.natDegree := rfl
    rw [hsum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [hfib d hd, Finset.sum_const_nat (fun q hq => (hprop d hd q hq).2.1),
      (Finset.mem_powersetCard.mp (hf d hd)).2, mul_comm]
  have hTval : ∀ c : Fin N → K, Squarefree (monicOf c) →
      (normalizedFactors (monicOf c)).toFinset.val = normalizedFactors (monicOf c) := by
    intro c hsq
    rw [Multiset.toFinset_val]
    exact Multiset.dedup_eq_self.mpr
      ((squarefree_iff_nodup_normalizedFactors (monicOf_monic c).ne_zero).mp hsq)
  refine (Finset.card_nbij' (t := (Finset.Icc 1 N).pi (fun d => (Irr d).powersetCard (n d)))
    (fun (c : Fin N → K) (d : ℕ) (_ : d ∈ Finset.Icc 1 N) =>
      (normalizedFactors (monicOf c)).toFinset.filter (fun q => q.natDegree = d))
    (fun (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (k : Fin N) => ((U f).val.prod).coeff k)
    ?_ ?_ ?_ ?_).trans ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, hcount⟩ := hc
    rw [Finset.mem_coe, Finset.mem_pi]
    intro d hd
    rw [Finset.mem_powersetCard]
    constructor
    · intro q hq
      rw [Finset.mem_filter, Multiset.mem_toFinset] at hq
      obtain ⟨h1, h2, h3, _, _⟩ := F c hc0 q hq.1
      exact (hIrr d q).mpr ⟨h1, hq.2, h2, h3⟩
    · have h := L2 (normalizedFactors (monicOf c)).toFinset d
      rw [hTval c hsq] at h
      rw [← h]
      exact hcount d hd
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, hc0, hfib⟩ := key f hf
    have hp := monicOf_coeffs hmon hdeg
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter]
    dsimp only
    rw [hp]
    refine ⟨Finset.mem_univ _, (squarefree_iff_nodup_normalizedFactors hmon.ne_zero).mpr ?_, hc0, ?_⟩
    · rw [hnf]
      exact (U f).nodup
    · intro d hd
      rw [hnf, L2, hfib d hd]
      exact (Finset.mem_powersetCard.mp (hf d hd)).2
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, _⟩ := hc
    have hU : U (fun d _ => (normalizedFactors (monicOf c)).toFinset.filter
        (fun q => q.natDegree = d)) = (normalizedFactors (monicOf c)).toFinset := by
      ext q
      simp only [U]
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨x, _, hq⟩
        exact (Finset.mem_filter.mp hq).1
      · intro hq
        obtain ⟨_, _, _, h4, h5⟩ := F c hc0 q (Multiset.mem_toFinset.mp hq)
        exact ⟨⟨q.natDegree, Finset.mem_Icc.mpr ⟨h4, h5⟩⟩, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    funext k
    dsimp only
    rw [hU, hTval c hsq, P c hc0, monicOf_coeff]
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, _, hfib⟩ := key f hf
    funext d hd
    dsimp only
    rw [monicOf_coeffs hmon hdeg, hnf, Finset.val_toFinset, hfib d hd]
  · rw [Finset.card_pi]
    refine Finset.prod_congr rfl ?_
    intro d _
    rw [Finset.card_powersetCard]
    simp only [Irr]
    rw [Finset.card_image_of_injective _ monicOf_injective]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.ProdPowFactorizationLe
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (h : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ (s = ∅ ∨ 2 ≤ ∏ l ∈ s, f l) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h' : ∀ l ∈ s, 2 ≤ f l := fun l hl => h l (Finset.mem_insert_of_mem hl)
    obtain ⟨ih1, ih2⟩ := ih h'
    have hfa := h a (Finset.mem_insert_self a s)
    have hpos : 0 < ∏ l ∈ s, f l := Finset.prod_pos (fun l hl => by have := h' l hl; omega)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, Or.inr (by nlinarith)⟩
    rcases ih2 with rfl | h2
    · simp
    · nlinarith

private theorem prod_pow_factorization_le (s : Finset ℕ) (n : ℕ) (hn : n ≠ 0) (hs : ∀ l ∈ s, l.Prime) :
    ∏ l ∈ s, l ^ n.factorization l ≤ n := by
  classical
  calc ∏ l ∈ s, l ^ n.factorization l ≤ ∏ l ∈ s ∪ n.primeFactors, l ^ n.factorization l := by
        apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
        intro l hl _
        rcases Finset.mem_union.1 hl with h | h
        · exact Nat.one_le_pow _ _ (hs l h).pos
        · exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors h).pos
    _ = ∏ l ∈ n.primeFactors, l ^ n.factorization l := by
        symm
        apply Finset.prod_subset Finset.subset_union_right
        intro l _ hl
        have : n.factorization l = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hl
        rw [this, pow_zero]
    _ = n := by
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
        rfl

private theorem lte_val (g δ l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hδ : 1 ≤ δ) (hl : l.Prime)
    (hd : l ∣ g - 1) : padicValNat l (g ^ δ - 1) = padicValNat l (g - 1) + padicValNat l δ := by
  have : Fact l.Prime := ⟨hl⟩
  have hlg : ¬ l ∣ g := by
    intro h
    have : l ∣ 1 := by
      have h2 : l ∣ g - (g - 1) := Nat.dvd_sub h hd
      have : g - (g - 1) = 1 := by omega
      rwa [this] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hgz : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
      rw [← this]; exact_mod_cast h4
    have hg2 : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg
    have key := Int.two_pow_sub_pow' (x := (g : ℤ)) (y := 1) δ hgz hg2
    have hpos : 1 ≤ g ^ δ := Nat.one_le_pow _ _ (by omega)
    have e1 : ((g : ℤ) ^ δ - 1 ^ δ) = ((g ^ δ - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hpos]; ring
    have e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
    rw [e1, e2] at key
    have c2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [c2, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have n1 : g ^ δ - 1 ≠ 0 := by
      have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
      simp at this; omega
    rw [← padicValNat_eq_emultiplicity n1, ← padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0),
      ← padicValNat_eq_emultiplicity (by omega : δ ≠ 0)] at key
    simp only [Nat.padicValNat_def]
    exact_mod_cast key
  · have := padicValNat.pow_sub_pow (p := l) hodd (x := g) (y := 1) (by omega) hd hlg (n := δ) (by omega)
    simpa [Nat.padicValNat_def] using this

theorem prime_power_order_count : PrimePowerOrderCount := by
  classical
  intro g δ hg h4 hδ
  set A := g - 1 with hA
  have hA0 : A ≠ 0 := by omega
  obtain ⟨B, hB⟩ : A ∣ g ^ δ - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 δ
  have n1 : g ^ δ - 1 ≠ 0 := by
    have : g ^ 1 ≤ g ^ δ := Nat.pow_le_pow_right (by omega) hδ
    simp at this; omega
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB; exact n1 hB
  have hdiv : (g ^ δ - 1) / A = B := by rw [hB]; exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv, ← Finset.sum_filter_add_sum_filter_not _ (fun l => l ∣ A)]
  apply add_le_add
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ (δ * A).factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [lte_val g δ l hg h4 hδ hp hl.2, Nat.padicValNat_def, Nat.padicValNat_def, Nat.factorization_mul (by omega) hA0,
        Finsupp.add_apply, Nat.factorization_def _ hp, Nat.factorization_def _ hp, add_comm]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _
      (Nat.mul_ne_zero (by omega) hA0) ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have : 1 ≤ (δ * A).factorization l :=
        (hp.dvd_iff_one_le_factorization (Nat.mul_ne_zero (by omega) hA0)).1 (Dvd.dvd.mul_left hl.2 _)
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1
  · have e : ∀ l ∈ (g ^ δ - 1).primeFactors.filter (fun l => ¬ l ∣ A),
        l ^ padicValNat l (g ^ δ - 1) = l ^ B.factorization l := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp, hB, Nat.factorization_mul hA0 hB0]
      have : A.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hl.2
      simp [this]
    rw [Finset.sum_congr rfl e]
    refine le_trans (sum_le_prod_of_two_le _ _ ?_).1 (prod_pow_factorization_le _ _ hB0 ?_)
    · intro l hl
      rw [Finset.mem_filter] at hl
      have hp := Nat.prime_of_mem_primeFactors hl.1
      have hd : l ∣ B := by
        have := Nat.dvd_of_mem_primeFactors hl.1
        rw [hB] at this
        exact (hp.dvd_mul.1 this).resolve_left hl.2
      have : 1 ≤ B.factorization l := (hp.dvd_iff_one_le_factorization hB0).1 hd
      calc 2 ≤ l := hp.two_le
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ _ := Nat.pow_le_pow_right hp.pos this
    · intro l hl
      exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hl).1

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

