module

public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0004

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.FourMulSumLeProduct
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ 1 ≤ ∏ l ∈ s, f l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
    have hfa : 2 ≤ f a := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, by nlinarith⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨b, hb⟩
    · subst hs
      simp
    · have hP2 : 2 ≤ ∏ l ∈ s, f l :=
        (hf b (Finset.mem_insert_of_mem hb)).trans
          (Finset.single_le_prod' (fun l hl => by
            have := hf l (Finset.mem_insert_of_mem hl)
            omega) hb)
      nlinarith

private theorem one_sub_sum_mul_prod_le_prod (q x y z T P : ℕ) (hx : 16 ≤ x) (hy : q ≤ y) (hz : 16 ≤ z) (hqz : q ≤ z)
    (hT : T ≤ P) (hP : 1 ≤ P) : 4 * q * (x + (y + (z + T))) ≤ x * (y * (z * P)) := by
  have h1 : 16 * q ≤ y * z * P := by
    calc 16 * q = q * 16 * 1 := by ring
      _ ≤ y * z * P := Nat.mul_le_mul (Nat.mul_le_mul hy hz) hP
  have h2 : 16 * q ≤ x * z * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * z * P := Nat.mul_le_mul (Nat.mul_le_mul hx hqz) hP
  have h3 : 16 * q ≤ x * y * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * y * P := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hP
  have h4 : 16 * q * T ≤ x * y * z * P := by
    have h5 : 16 * q ≤ x * y * z := by
      calc 16 * q = 16 * q * 1 := by ring
        _ ≤ x * y * z := Nat.mul_le_mul (Nat.mul_le_mul hx hy) (by omega)
    exact Nat.mul_le_mul h5 hT
  nlinarith [Nat.mul_le_mul_left x h1, Nat.mul_le_mul_left y h2, Nat.mul_le_mul_left z h3]

theorem prime_power_order_share : PrimePowerOrderShare := by
  intro g q₁ d hg hq hd hqd hq2 hd2 hM h16 hqn hdn
  set n := g - 1 with hn
  have hn0 : n ≠ 0 := by omega
  have h2n : 2 ∣ n := (show 2 ∣ 16 by norm_num).trans h16
  have hmem : ∀ l, l.Prime → l ∣ n → l ∈ n.primeFactors := fun l hl hln =>
    Nat.mem_primeFactors.mpr ⟨hl, hln, hn0⟩
  have hge : ∀ l, l.Prime → l ∣ n → l ≤ l ^ padicValNat l n := by
    intro l hl hln
    haveI := Fact.mk hl
    have hv : 1 ≤ padicValNat l n := by
      simpa only [Nat.padicValNat_def] using one_le_multiplicity_of_dvd hn0 hln
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ padicValNat l n := Nat.pow_le_pow_right hl.pos hv
  have hf2 : 16 ≤ 2 ^ padicValNat 2 n := by
    haveI := Fact.mk Nat.prime_two
    have hv : 4 ≤ padicValNat 2 n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn0).mp (by norm_num; exact h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) hv
  have h2m := hmem 2 Nat.prime_two h2n
  have hqm : q₁ ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨hq2, hmem q₁ hq hqn⟩
  have hdm : d ∈ (n.primeFactors.erase 2).erase q₁ :=
    Finset.mem_erase.mpr ⟨fun h => hqd h.symm, Finset.mem_erase.mpr ⟨hd2, hmem d hd hdn⟩⟩
  have hsum : ∑ l ∈ n.primeFactors, l ^ padicValNat l n =
      2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
        ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    rw [← Finset.add_sum_erase _ _ h2m, ← Finset.add_sum_erase _ _ hqm, ← Finset.add_sum_erase _ _ hdm]
  have hprod : n = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
        ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    have h1 : ∏ l ∈ n.primeFactors, l ^ padicValNat l n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hl), Nat.padicValNat_def]
    rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ hqm,
      ← Finset.mul_prod_erase _ _ hdm] at h1
    exact h1.symm
  have hR2 : ∀ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, 2 ≤ l ^ padicValNat l n := by
    intro l hl
    have hl' : l ∈ n.primeFactors :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
    have hlp := Nat.prime_of_mem_primeFactors hl'
    exact hlp.two_le.trans (hge l hlp (Nat.dvd_of_mem_primeFactors hl'))
  obtain ⟨hTP, hP1⟩ := sum_le_prod_of_two_le _ (fun l => l ^ padicValNat l n) hR2
  have hq16 := hge q₁ hq hqn
  have hd16 := hge d hd hdn
  have hnat : (∑ l ∈ n.primeFactors, l ^ padicValNat l n) * (4 * min q₁ d) ≤ n := by
    rw [hsum]
    rcases le_total q₁ d with hle | hle
    · rw [min_eq_left hle]
      have key := one_sub_sum_mul_prod_le_prod q₁ _ _ _ _ _ hf2 hq16 (le_trans (by omega : 16 ≤ d) hd16)
        (hle.trans hd16) hTP hP1
      calc _ = 4 * q₁ * (2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = n := hprod.symm
    · rw [min_eq_right hle]
      have key := one_sub_sum_mul_prod_le_prod d (2 ^ padicValNat 2 n) (d ^ padicValNat d n) (q₁ ^ padicValNat q₁ n) _ _
        hf2 hd16 (le_trans (by omega : 16 ≤ q₁) hq16) (hle.trans hq16) hTP hP1
      calc _ = 4 * d * (2 ^ padicValNat 2 n + (d ^ padicValNat d n + (q₁ ^ padicValNat q₁ n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
            ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by ring
        _ = n := hprod.symm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hmpos : (0 : ℝ) < 4 * ((min q₁ d : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_min hq.pos hd.pos))
  rw [← Nat.cast_sum, div_le_div_iff₀ hnpos hmpos, one_mul]
  exact_mod_cast hnat

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_lpow_add {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by
  rw [pow_add, pow_mul, pow_mul, h]

theorem eq_of_pow_eq_of_coprime_order {M : Type*} [Monoid M] {r : ℕ} {u w : M}
    (hu : 0 < orderOf u) (hw : 0 < orderOf w) (hcu : Nat.Coprime r (orderOf u))
    (hcw : Nat.Coprime r (orderOf w)) (h : u ^ r = w ^ r) : u = w := by
  by_cases h1 : orderOf u * orderOf w = 1
  · have hu1 : orderOf u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hw1 : orderOf w = 1 := Nat.eq_one_of_mul_eq_one_left h1
    rw [orderOf_eq_one_iff.mp hu1, orderOf_eq_one_iff.mp hw1]
  · have hpos : 0 < orderOf u * orderOf w := Nat.mul_pos hu hw
    have hlt : 1 < orderOf u * orderOf w := by omega
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.mul_right hcu hcw) hlt
    have hmod : r * s ≡ 1 [MOD orderOf u * orderOf w] := by
      unfold Nat.ModEq
      rw [hs, Nat.mod_eq_of_lt hlt]
    have hm1 : r * s ≡ 1 [MOD orderOf u] := Nat.ModEq.of_mul_right (orderOf w) hmod
    have hm2 : r * s ≡ 1 [MOD orderOf w] := Nat.ModEq.of_mul_left (orderOf u) hmod
    have hu' : u ^ (r * s) = u := by
      rw [← pow_mod_orderOf, show r * s % orderOf u = 1 % orderOf u from hm1, pow_mod_orderOf,
        pow_one]
    have hw' : w ^ (r * s) = w := by
      rw [← pow_mod_orderOf, show r * s % orderOf w = 1 % orderOf w from hm2, pow_mod_orderOf,
        pow_one]
    rw [← hu', ← hw', pow_mul, pow_mul, h]

theorem prime_to_part_eq_iff : PrimeToPartEqIff := by
  intro M _ l x y hl hx hy
  obtain ⟨hox, a, ha⟩ := prime_to_part_spec M l x hl hx
  obtain ⟨hoy, b, hb⟩ := prime_to_part_spec M l y hl hy
  have hnx : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  have hny : orderOf y ≠ 0 := (orderOf_pos_iff.mpr hy).ne'
  constructor
  · intro h
    refine ⟨a + b, ?_⟩
    rw [pow_lpow_add ha b, h, add_comm a b, pow_lpow_add hb a]
  · rintro ⟨c, hc⟩
    have e1 : primeToPart l x ^ (l ^ (a + (b + c))) = x ^ (l ^ (a + (b + c))) :=
      (pow_lpow_add ha _).symm
    have e2 : primeToPart l y ^ (l ^ (b + (a + c))) = y ^ (l ^ (b + (a + c))) :=
      (pow_lpow_add hb _).symm
    have e3 : x ^ (l ^ (c + (a + b))) = y ^ (l ^ (c + (a + b))) := pow_lpow_add hc _
    have s1 : a + (b + c) = c + (a + b) := by omega
    have s2 : b + (a + c) = c + (a + b) := by omega
    rw [s1] at e1
    rw [s2] at e2
    refine eq_of_pow_eq_of_coprime_order (r := l ^ (c + (a + b))) ?_ ?_ ?_ ?_ (by rw [e1, e2, e3])
    · rw [hox]; exact Nat.ordCompl_pos l hnx
    · rw [hoy]; exact Nat.ordCompl_pos l hny
    · rw [hox]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnx)
    · rw [hoy]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hny)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.IRRSquarefreeCount
section
open Polynomial
open scoped Classical

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


open Classical in
theorem card_mult_le {K : Type} [Field K] [Fintype K] (N j : ℕ) (P : K[X]) (hP : P.Monic)
    (hj : P.natDegree = j) :
    ((Finset.univ : Finset (Fin N → K)).filter (fun c => P * P ∣ monicOf c)).card
      ≤ Fintype.card K ^ (N - 2 * j) := by
  have hPP : (P * P).Monic := hP.mul hP
  have hcard : Fintype.card (Fin (N - 2 * j) → K) = Fintype.card K ^ (N - 2 * j) := by simp
  rw [← hcard, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn
    (fun c => fun i : Fin (N - 2 * j) => ((monicOf c) /ₘ (P * P)).coeff i)
  · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · have key : ∀ c : Fin N → K, P * P ∣ monicOf c →
        ((monicOf c) /ₘ (P * P)).Monic ∧ ((monicOf c) /ₘ (P * P)).natDegree = N - 2 * j ∧
        monicOf c = P * P * ((monicOf c) /ₘ (P * P)) := by
      intro c hc
      obtain ⟨g, hg⟩ := hc
      have hdiv : (monicOf c) /ₘ (P * P) = g := by
        rw [hg]; exact mul_divByMonic_cancel_left g hPP
      have hgm : g.Monic := hPP.of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P * P).natDegree + g.natDegree := by
        rw [hg]; exact hPP.natDegree_mul hgm
      rw [monicOf_natDegree, hP.natDegree_mul hP, hj] at hdeg
      rw [hdiv]
      exact ⟨hgm, by omega, hg⟩
    intro c hc c' hc' h
    obtain ⟨h1, h2, h3⟩ := key c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    obtain ⟨h1', h2', h3'⟩ := key c' (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
    apply monicOf_injective
    rw [h3, h3', ← monicOf_coeffs h1 h2, ← monicOf_coeffs h1' h2']
    exact congrArg (fun v => P * P * monicOf v) h

theorem geom_tail (q N m : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) (hm : m ≤ N) :
    ∑ j ∈ Finset.Icc 2 m, q ^ (N - j) ≤ 2 * q ^ (N - 2) := by
  have key : ∀ m, 1 ≤ m → m ≤ N →
      (∑ j ∈ Finset.Icc 2 m, q ^ (N - j)) * (q - 1) + q ^ (N - m) = q ^ (N - 1) := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h1 h2
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · rw [Finset.sum_Icc_succ_top (by omega), add_mul, add_assoc]
        have e : q ^ (N - (m + 1)) * (q - 1) + q ^ (N - (m + 1)) = q ^ (N - m) := by
          have h3 : N - m = (N - (m + 1)) + 1 := by omega
          rw [h3, pow_succ, ← Nat.mul_succ]
          congr 1
          omega
        rw [e]
        exact ih hm (by omega)
  by_cases hm1 : 1 ≤ m
  · have h := key m hm1 hm
    have hN1 : q ^ (N - 1) = q ^ (N - 2) * q := by
      rw [← pow_succ]; congr 1; omega
    obtain ⟨p, hp⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    subst hp
    have hq1 : p + 2 - 1 = p + 1 := by omega
    rw [hq1, hN1] at h
    set S := ∑ j ∈ Finset.Icc 2 m, (p + 2) ^ (N - j)
    set Q := (p + 2) ^ (N - 2)
    by_contra hc
    push_neg at hc
    have h4 := Nat.mul_le_mul_right (p + 1) (show 2 * Q + 1 ≤ S by omega)
    clear_value S Q
    ring_nf at h h4
    nlinarith [Nat.zero_le (p * Q), Nat.zero_le ((2 + p) ^ (N - m))]
  · have : m = 0 := by omega
    subst this
    simp

theorem squarefree_count : SquarefreeCount := by
  classical
  intro K _ _ N hN
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set Ω := (Finset.univ : Finset (Fin N → K)) with hΩ
  set Good := Ω.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hGood
  set Bad0 := Ω.filter (fun c => (monicOf c).coeff 0 = 0) with hBad0
  set BadS := Ω.filter (fun c => ¬ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hBadS
  have hΩcard : Ω.card = q ^ N := by simp [hΩ, hq]
  have hcover : Ω ⊆ Good ∪ (Bad0 ∪ BadS) := by
    intro c hc
    simp only [hGood, hBad0, hBadS, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : (monicOf c).coeff 0 = 0
    · exact Or.inr (Or.inl ⟨hc, h0⟩)
    · by_cases hs : Squarefree (monicOf c)
      · exact Or.inl ⟨hc, hs, h0⟩
      · exact Or.inr (Or.inr ⟨hc, hs, h0⟩)
  have hB0 : Bad0.card ≤ q ^ (N - 1) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hcard : Fintype.card (Fin M → K) = q ^ (M + 1 - 1) := by simp [hq]
    rw [← hcard, ← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun c => Fin.tail c)
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro c hc c' hc' h
      have h0 : c 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
        rwa [← monicOf_coeff c 0]
      have h0' : c' 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
        rwa [← monicOf_coeff c' 0]
      rw [← Fin.cons_self_tail c, ← Fin.cons_self_tail c', h0, h0']
      exact congrArg (Fin.cons 0) h
  set I : ℕ → ℕ := fun j => ((Finset.univ : Finset (Fin j → K)).filter
      (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).card with hI
  have hBS : BadS.card ≤ ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) := by
    have hsub : BadS ⊆ (Finset.Icc 1 (N / 2)).biUnion (fun j =>
        ((Finset.univ : Finset (Fin j → K)).filter
          (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).biUnion (fun p =>
            Ω.filter (fun c => monicOf p * monicOf p ∣ monicOf c))) := by
      intro c hc
      obtain ⟨_, hns, h0⟩ := Finset.mem_filter.mp hc
      have hne : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
      rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hne] at hns
      push Not at hns
      obtain ⟨P, hPirr, hPdvd⟩ := hns
      set P' := normalize P with hP'
      have hass : Associated P' P := normalize_associated P
      have hP'irr : Irreducible P' := hass.symm.irreducible hPirr
      have hP'mon : P'.Monic := monic_normalize hPirr.ne_zero
      have hP'dvd : P' * P' ∣ monicOf c :=
        (mul_dvd_mul hass.dvd hass.dvd).trans hPdvd
      obtain ⟨g, hg⟩ := hP'dvd
      have hgm : g.Monic := (hP'mon.mul hP'mon).of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P' * P').natDegree + g.natDegree := by
        rw [hg]; exact (hP'mon.mul hP'mon).natDegree_mul hgm
      rw [monicOf_natDegree, hP'mon.natDegree_mul hP'mon] at hdeg
      have hj1 : 1 ≤ P'.natDegree := hP'irr.natDegree_pos
      have hc0 : P'.coeff 0 ≠ 0 := by
        intro hz
        apply h0
        rw [hg, mul_coeff_zero, mul_coeff_zero, hz]
        simp
      refine Finset.mem_biUnion.mpr ⟨P'.natDegree, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨fun i => P'.coeff i, ?_, ?_⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, hP'irr, hc0⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, ⟨g, hg⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    apply Finset.sum_le_sum
    intro j _
    refine Finset.card_biUnion_le.trans ?_
    rw [hI]
    simp only
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p _
    exact card_mult_le N j (monicOf p) (monicOf_monic p) (monicOf_natDegree p)
  have hI1 : I 1 ≤ q - 1 := by
    have hsub : ((Finset.univ : Finset (Fin 1 → K)).filter
        (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)) ⊆
        (Finset.univ : Finset (Fin 1 → K)).erase 0 := by
      intro p hp
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      have := (Finset.mem_filter.mp hp).2.2
      apply this
      have h := monicOf_coeff (0 : Fin 1 → K) 0
      simpa using h
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    simpa [hI, hq] using this
  have hI2 : ∀ j, 2 ≤ j → 2 * I j ≤ q ^ j := by
    intro j hj
    have h1 := irreducible_count_upper K j (by omega)
    have h2 : I j ≤ ((Finset.univ : Finset (Fin j → K)).filter
        (fun c => Irreducible (monicOf c))).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩
    calc 2 * I j ≤ j * I j := Nat.mul_le_mul_right _ hj
      _ ≤ j * _ := Nat.mul_le_mul_left _ h2
      _ ≤ q ^ j := h1
  have hsum : ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) ≤ q ^ (N - 1) := by
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · have : N / 2 = 0 := by omega
      rw [this]; simp
    · have hm1 : 1 ≤ N / 2 := by omega
      rw [← Finset.add_sum_Ioc_eq_sum_Icc hm1]
      have hIoc : Finset.Ioc 1 (N / 2) = Finset.Icc 2 (N / 2) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      rw [hIoc]
      have h2 : 2 * ∑ j ∈ Finset.Icc 2 (N / 2), I j * q ^ (N - 2 * j) ≤ 2 * q ^ (N - 2) := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) (geom_tail q N (N / 2) hq2 hge
          (Nat.div_le_self _ _))
        obtain ⟨hj2, hjm⟩ := Finset.mem_Icc.mp hj
        calc 2 * (I j * q ^ (N - 2 * j)) = (2 * I j) * q ^ (N - 2 * j) := by ring
          _ ≤ q ^ j * q ^ (N - 2 * j) := Nat.mul_le_mul_right _ (hI2 j hj2)
          _ = q ^ (N - j) := by rw [← pow_add]; congr 1; omega
      have h3 : I 1 * q ^ (N - 2 * 1) ≤ (q - 1) * q ^ (N - 2) := Nat.mul_le_mul_right _ hI1
      have h4 : q ^ (N - 1) = (q - 1) * q ^ (N - 2) + q ^ (N - 2) := by
        have : N - 1 = (N - 2) + 1 := by omega
        rw [this, pow_succ]
        obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        rw [hr]
        simp only [Nat.add_sub_cancel]
        ring
      omega
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le Good (Bad0 ∪ BadS)
  have h3 := Finset.card_union_le Bad0 BadS
  rw [hΩcard] at h1
  have h5 := hBS.trans hsum
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

