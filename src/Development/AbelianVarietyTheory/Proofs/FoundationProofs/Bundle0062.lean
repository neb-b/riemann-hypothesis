module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardIrreducibleSamePrimeToPartRootsLe
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.TwoRoots

theorem pow_card_pow_natDegree {g : ℕ} [Fact g.Prime] (x : AlgebraicClosure (ZMod g)) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI : Fintype (IntermediateField.adjoin (ZMod g) {x}) := Fintype.ofFinite _
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := FiniteField.pow_card y
  rw [Module.card_eq_pow_finrank (K := ZMod g), IntermediateField.adjoin.finrank hi, ZMod.card] at h
  simpa [y] using congrArg Subtype.val h

theorem pow_eq_pow_padicVal {k : Type} [Field k] {n l a : ℕ} (hn : n ≠ 0) (hl : l.Prime) {x y : k}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (h : x ^ (l ^ a) = y ^ (l ^ a)) :
    x ^ (l ^ padicValNat l n) = y ^ (l ^ padicValNat l n) := by
  haveI := Fact.mk hl
  have hy0 : y ≠ 0 := by rintro rfl; simp [hn] at hy
  have h1 : (x / y) ^ n = 1 := by rw [div_pow, hx, hy, div_one]
  have h2 : (x / y) ^ (l ^ a) = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hy0)]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h2)
  have h3 : l ^ b ∣ n := hb ▸ orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (x / y) ∣ l ^ padicValNat l n := by
    rw [hb]; exact pow_dvd_pow _ (((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn).1 h3)
  have h5 := orderOf_dvd_iff_pow_eq_one.1 h4
  rwa [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hy0)] at h5

theorem exists_small_degree {g : ℕ} [Fact g.Prime] {x y : AlgebraicClosure (ZMod g)} {L : ℕ}
    (hm : minpoly (ZMod g) x = minpoly (ZMod g) y) (hxy : x ≠ y) (h : x ^ L = y ^ L) :
    ∃ e, 1 ≤ e ∧ e ≤ (minpoly (ZMod g) x).natDegree / 2 ∧ (x ^ L) ^ (g ^ e) = x ^ L := by
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hz : IsIntegral (ZMod g) (x ^ L) := Algebra.IsIntegral.isIntegral _
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI := IntermediateField.adjoin.finiteDimensional hz
  refine ⟨(minpoly (ZMod g) (x ^ L)).natDegree, minpoly.natDegree_pos hz, ?_, pow_card_pow_natDegree _⟩
  have hle : IntermediateField.adjoin (ZMod g) {x ^ L} ≤ IntermediateField.adjoin (ZMod g) {x} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  have hdvd := IntermediateField.finrank_dvd_of_le_right hle
  have hne : Module.finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {x ^ L}) ≠
      Module.finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) := by
    intro he
    have heq := IntermediateField.eq_of_le_of_finrank_eq hle he
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv (show IsConjRoot (ZMod g) y x from hm.symm)
    have hx : x ∈ IntermediateField.adjoin (ZMod g) {x ^ L} := heq ▸ IntermediateField.mem_adjoin_simple_self _ _
    have hfix : IntermediateField.adjoin (ZMod g) {x ^ L} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, ← IntermediateField.adjoin_simple_le_iff,
        IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
      intro t ht
      induction ht using IntermediateField.adjoin_induction with
      | mem t ht => rw [Set.mem_singleton_iff.1 ht, map_pow, hσ, h]
      | algebraMap t => exact σ.commutes t
      | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
      | inv a _ ha => rw [map_inv₀, ha]
      | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    have := (IntermediateField.mem_fixedField_iff _ _).1 (hfix hx) σ (Subgroup.mem_zpowers σ)
    exact hxy (this.symm.trans hσ)
  rw [IntermediateField.adjoin.finrank hi, IntermediateField.adjoin.finrank hz] at hdvd hne
  obtain ⟨c, hc⟩ := hdvd
  have hpos := minpoly.natDegree_pos hi
  rw [Nat.le_div_iff_mul_le two_pos, hc]
  apply Nat.mul_le_mul_left
  rcases c with _ | _ | c
  · omega
  · omega
  · omega

theorem sum_pow_le {g : ℕ} (hg : 2 ≤ g) (m : ℕ) : ∑ e ∈ Finset.Icc 1 m, g ^ e ≤ 2 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    nlinarith [Nat.zero_le (g ^ m)]

theorem card_le_nat (g : ℕ) [Fact g.Prime] (d l : ℕ) (hd : 2 ≤ d) (hl : l.Prime) :
    ((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card ≤
      l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  set S := (sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y with hS
  set L := l ^ padicValNat l (g ^ d - 1) with hL
  have hL0 : 0 < L := pow_pos hl.pos _
  let Q : ℕ → (AlgebraicClosure (ZMod g))[X] := fun e => X ^ (L * g ^ e) - X ^ L
  have hQ : ∀ e, 1 ≤ e → (Q e).natDegree = L * g ^ e := by
    intro e he
    have : 1 < g ^ e := Nat.one_lt_pow (by omega) hg
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow, natDegree_X_pow]; nlinarith
  let B : Finset (AlgebraicClosure (ZMod g)) := (Finset.Icc 1 (d / 2)).biUnion fun e => (Q e).roots.toFinset
  have hB : B.card ≤ 2 * (L * g ^ (d / 2)) := by
    calc B.card ≤ ∑ e ∈ Finset.Icc 1 (d / 2), (Q e).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ Finset.Icc 1 (d / 2), L * g ^ e := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [← hQ e (Finset.mem_Icc.1 he).1]
        exact (Multiset.toFinset_card_le _).trans (card_roots' _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        have := Nat.mul_le_mul_left L (sum_pow_le hg (d / 2))
        linarith
  have hmemB : ∀ x y : AlgebraicClosure (ZMod g), minpoly (ZMod g) x = minpoly (ZMod g) y →
      (minpoly (ZMod g) x).natDegree = d → x ≠ y → x ^ L = y ^ L → x ∈ B := by
    intro x y h1 h2 h3 h4
    obtain ⟨e, he1, he2, he3⟩ := exists_small_degree h1 h3 h4
    rw [h2] at he2
    refine Finset.mem_biUnion.2 ⟨e, Finset.mem_Icc.2 ⟨he1, he2⟩, ?_⟩
    have hQ0 : Q e ≠ 0 := by
      intro h0
      have := hQ e he1
      rw [h0, natDegree_zero] at this
      have : 0 < L * g ^ e := by positivity
      omega
    rw [Multiset.mem_toFinset, mem_roots hQ0]
    simp [Q, pow_mul, he3]
  have hcount : 2 * S.card ≤ (B.filter fun x => minpoly (ZMod g) x ∈ S).card := by
    refine Finset.mul_card_image_le_card_of_maps_to (f := fun x => minpoly (ZMod g) x)
      (fun a ha => (Finset.mem_filter.1 ha).2) 2 ?_
    intro P hP
    obtain ⟨hP1, hirr, x, hx, y, hy, hxy, hs⟩ := Finset.mem_filter.1 hP
    obtain ⟨hmon, hdeg, -, h0⟩ := mem_sqSet.1 hP1
    have ex := (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hx).2 hmon).symm
    have ey := (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hmon).symm
    have hx0 := root_ne_zero h0 hx
    have hy0 := root_ne_zero h0 hy
    have hgd : 1 < g ^ d := Nat.one_lt_pow (by omega) hg
    have hroot : ∀ t : AlgebraicClosure (ZMod g), t ≠ 0 → minpoly (ZMod g) t = P → t ^ (g ^ d - 1) = 1 := by
      intro t ht et
      have := pow_card_pow_natDegree t
      rw [et, hdeg] at this
      apply mul_right_cancel₀ ht
      rw [← pow_succ, Nat.sub_add_cancel hgd.le, this, one_mul]
    obtain ⟨a, ha⟩ := (samePart_iff_of_ne_zero hl hx0 hy0).1 hs
    have hLxy : x ^ L = y ^ L := pow_eq_pow_padicVal (by omega) hl (hroot x hx0 ex) (hroot y hy0 ey) ha
    have hxB := hmemB x y (ex.trans ey.symm) (by rw [ex, hdeg]) hxy hLxy
    have hyB := hmemB y x (ey.trans ex.symm) (by rw [ey, hdeg]) hxy.symm hLxy.symm
    rw [← Finset.card_pair hxy]
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_filter]
    rcases ht with rfl | rfl
    · exact ⟨⟨hxB, by rw [ex]; exact hP⟩, ex⟩
    · exact ⟨⟨hyB, by rw [ey]; exact hP⟩, ey⟩
  have := hcount.trans ((Finset.card_filter_le _ _).trans hB)
  omega

theorem card_irreducible_samePart_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by
  intro g _ N d l hd hN hl hb
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have h1 := card_le_nat g d l hd hl
  have h2 : (l ^ padicValNat l (g ^ d - 1)) ^ 4 ≤ g ^ d := by
    by_contra hc
    exact hb (bb_iff.2 (Or.inr ⟨hl, d, by omega, hN, by rw [mul_comm, pow_mul]; omega⟩))
  have h3 : ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    rw [← Real.rpow_natCast ((g : ℝ) ^ ((d : ℝ) / 4)), ← Real.rpow_mul (by positivity)]
    have : (d : ℝ) / 4 * (4 : ℕ) = d := by push_cast; ring
    rw [this, Real.rpow_natCast]
    exact_mod_cast h2
  have h4 : ((g ^ (d / 2) : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by exact_mod_cast Nat.cast_div_le (α := ℝ) (m := d) (n := 2))
  calc _ ≤ ((l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (g : ℝ) ^ ((d : ℝ) / 4) * (g : ℝ) ^ ((d : ℝ) / 2) := by
      rw [Nat.cast_mul]; exact mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end GlobalTheory.BadShare.TwoRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermPartitionPartsMulCentralizer
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

private lemma eq_filter_add_replicate (μ : Multiset ℕ) (h : ∀ d ∈ μ, 0 < d) :
    μ = μ.filter (fun n => 2 ≤ n) + Multiset.replicate (μ.count 1) 1 := by
  ext d
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases h2 : 2 ≤ d
  · rw [if_pos h2, if_neg (by omega)]; rfl
  · rw [if_neg h2]
    by_cases h1 : 1 = d
    · subst h1; simp
    · rw [if_neg h1]
      have : d ∉ μ := fun hd => by have := h d hd; omega
      simpa using this

theorem card_perm_partition_parts_mul :
    ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N →
      (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card *
        ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  intro N μ hpos hsum
  set m := μ.filter (fun n => 2 ≤ n) with hm
  have hμ : μ = m + Multiset.replicate (μ.count 1) 1 := eq_filter_add_replicate μ hpos
  have hs : m.sum + μ.count 1 = N := by
    rw [← hsum]
    conv_rhs => rw [hμ]
    simp
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin N) m
  rw [if_pos ⟨by rw [Fintype.card_fin]; omega, fun a ha => (Multiset.mem_filter.1 ha).2⟩,
    Fintype.card_fin] at key
  have hN : N - m.sum = μ.count 1 := by omega
  rw [hN] at key
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ) =
      Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.cycleType = m := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, h]
    · intro h
      rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, h, Fintype.card_fin, hN]
      exact hμ.symm
  have hprod : ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) =
      (μ.count 1).factorial * m.prod * ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [← Finset.prod_filter_mul_prod_filter_not μ.toFinset (fun n => 2 ≤ n)]
    have h1 : μ.toFinset.filter (fun n => 2 ≤ n) = m.toFinset := by
      ext n; simp [hm]
    have h2 : ∏ d ∈ μ.toFinset.filter (fun n => ¬ 2 ≤ n),
        (d ^ μ.count d * (μ.count d).factorial) = (μ.count 1).factorial := by
      rw [Finset.prod_eq_single 1]
      · simp
      · intro b hb hb1
        simp only [Finset.mem_filter, Multiset.mem_toFinset] at hb
        have := hpos b hb.1
        omega
      · intro h
        have : (1 : ℕ) ∉ μ := fun h1 => h (by simpa using h1)
        simp [Multiset.count_eq_zero_of_notMem this]
    rw [h1, h2, Finset.prod_multiset_count m, mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hn)).2
    have : m.count n = μ.count n := by rw [hm, Multiset.count_filter, if_pos hn2]
    rw [this]
  rw [hset, hprod]
  convert key

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

open Polynomial Classical in
private lemma centralBinom_le_pow_mul_four_pow_mul_prod_large_primes (m : ℕ) (hm : 2 < m) :
    m.centralBinom ≤ (2 * m) ^ (Nat.sqrt (2 * m) + 1) * 4 ^ (2 * m / 3) *
      ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p := by
  set s := Nat.sqrt (2 * m) with hs
  have hone : ∀ (P : Prop) [Decidable P] (p : ℕ), (P → 1 ≤ p) → 1 ≤ (if P then p else 1) := by
    intro P _ p h
    split_ifs with hP
    exacts [h hP, le_rfl]
  have key : ∀ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p ≤
      (if p ≤ s then 2 * m else 1) * (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := by
    intro p _
    have hB : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) :=
      hone _ _ fun h => h.1.one_lt.le
    have hC : 1 ≤ (if p.Prime ∧ m < p then p else 1) := hone _ _ fun h => h.1.one_lt.le
    have hBC : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := le_trans (by norm_num) (Nat.mul_le_mul hB hC)
    by_cases h1 : p ≤ s
    · rw [if_pos h1]
      have h2 : p ^ m.centralBinom.factorization p ≤ 2 * m := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le (by omega)
      calc p ^ m.centralBinom.factorization p ≤ 2 * m * 1 * 1 := by simpa using h2
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hB) hC
    · rw [if_neg h1, one_mul]
      have hsq : 2 * m < p ^ 2 :=
        calc 2 * m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' (2 * m)
          _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hv : m.centralBinom.factorization p ≤ 1 := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.factorization_choose_le_one hsq
      by_cases hp : p.Prime
      · by_cases h3 : p ≤ 2 * m / 3
        · have h4 : ¬ m < p := by omega
          rw [if_pos ⟨hp, h3⟩, if_neg (fun h => h4 h.2), mul_one]
          calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
            _ = p := pow_one p
        · by_cases h5 : m < p
          · rw [if_neg (fun h => h3 h.2), if_pos ⟨hp, h5⟩, one_mul]
            calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
              _ = p := pow_one p
          · have h0 : m.centralBinom.factorization p = 0 :=
              Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm (by omega) (by omega)
            rw [h0, pow_zero]
            exact hBC
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
        exact hBC
  calc m.centralBinom
      = ∏ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p :=
        (Nat.prod_pow_factorization_centralBinom m).symm
    _ ≤ ∏ p ∈ Finset.range (2 * m + 1), ((if p ≤ s then 2 * m else 1) *
          (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) * (if p.Prime ∧ m < p then p else 1)) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) key
    _ = (∏ p ∈ Finset.range (2 * m + 1), (if p ≤ s then 2 * m else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ m < p then p else 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
        gcongr ?_ * ?_ * ?_
        · rw [← Finset.prod_filter, Finset.prod_const]
          apply Nat.pow_le_pow_right (by omega)
          calc ((Finset.range (2 * m + 1)).filter (fun p => p ≤ s)).card
              ≤ (Finset.range (s + 1)).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
                omega
            _ = s + 1 := Finset.card_range _
        · rw [← Finset.prod_filter]
          calc ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ p ≤ 2 * m / 3), p
              = primorial (2 * m / 3) := by
                unfold primorial
                congr 1
                ext p
                simp only [Finset.mem_filter, Finset.mem_range]
                constructor
                · rintro ⟨_, h2, h3⟩
                  exact ⟨by omega, h2⟩
                · rintro ⟨h1, h2⟩
                  exact ⟨by omega, h2, by omega⟩
            _ ≤ 4 ^ (2 * m / 3) := primorial_le_four_pow _
        · rw [← Finset.prod_filter]


open Polynomial Classical in
theorem _root_.GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between :
    ∀ N : ℕ, 100000 ≤ N → 1 / (10 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hS
  set m := N / 2 with hm
  set s := Nat.sqrt (2 * m) with hs
  set k := S.card with hk
  set q := 2 * m / 3 with hq
  have hm3 : 2 < m := by omega
  have hT : ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p ≤
      N ^ 3 * N ^ k := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)) (· ∈ S), mul_comm]
    apply Nat.mul_le_mul
    · have hsub : ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
          (fun x => x ∉ S) ⊆ Finset.Icc (N - 2) N := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
        have h5 : ¬ (x + 3 ≤ N) := fun h5 => h4 (by
          rw [hS]
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, h2, by omega, h5⟩)
        rw [Finset.mem_Icc]
        omega
      calc _ ≤ N ^ (((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
            (fun x => x ∉ S)).card :=
            Finset.prod_le_pow_card _ _ _ (fun x hx => (Finset.mem_Icc.mp (hsub hx)).2)
        _ ≤ N ^ 3 := by
            apply Nat.pow_le_pow_right (by omega)
            calc _ ≤ (Finset.Icc (N - 2) N).card := Finset.card_le_card hsub
              _ = 3 := by rw [Nat.card_Icc]; omega
    · calc _ ≤ ∏ x ∈ S, x := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · intro x hx
              exact (Finset.mem_filter.mp hx).2
            · intro x hx _
              rw [hS] at hx
              exact (Finset.mem_filter.mp hx).2.1.one_lt.le
        _ ≤ N ^ k := Finset.prod_le_pow_card _ _ _ (fun x hx => by
            rw [hS] at hx
            have := (Finset.mem_filter.mp hx).1
            rw [Finset.mem_range] at this
            omega)
  have hnat : 4 ^ m < N ^ (s + 5 + k) * 4 ^ q := by
    calc 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m (by omega)
      _ ≤ N * ((2 * m) ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) :=
          Nat.mul_le_mul (by omega)
            (le_trans (centralBinom_le_pow_mul_four_pow_mul_prod_large_primes m hm3)
              (Nat.mul_le_mul_left _ hT))
      _ ≤ N * (N ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) := by
          gcongr
          omega
      _ = N ^ (s + 5 + k) * 4 ^ q := by ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hreal : (m : ℝ) * Real.log 4 < (s + 5 + k) * Real.log N + q * Real.log 4 := by
    have h' : (4 : ℝ) ^ m < (N : ℝ) ^ (s + 5 + k) * (4 : ℝ) ^ q := by exact_mod_cast hnat
    have h2 := Real.log_lt_log (by positivity) h'
    rw [Real.log_mul (pow_pos hN0 _).ne' (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow] at h2
    push_cast at h2
    linarith
  have hq3 : (3 : ℝ) * q ≤ 2 * m := by exact_mod_cast (by omega : 3 * q ≤ 2 * m)
  have hmN : (N : ℝ) ≤ 2 * m + 1 := by exact_mod_cast (by omega : N ≤ 2 * m + 1)
  have hs2 : (s : ℝ) ^ 2 ≤ N := by
    have : s ^ 2 ≤ N := le_trans (Nat.sqrt_le' (2 * m)) (by omega)
    exact_mod_cast this
  set t := Real.sqrt N with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = N := Real.sq_sqrt hN0.le
  have hNbig : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hst : (s : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have htlow : (316 : ℝ) ≤ t := by nlinarith
  have hL : Real.log N ≤ 7.72 + t / 50 := by
    have h1 := Real.log_le_sub_one_of_pos (x := t / 100) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    have h2 : Real.log t = Real.log N / 2 := by rw [ht, Real.log_sqrt hN0.le]
    have h3 : Real.log 100 < 4.86 := by
      have : Real.log 100 < Real.log (2 ^ 7) := Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at this
      push_cast at this
      linarith [Real.log_two_lt_d9]
    linarith
  have hL4 : 1.386 < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hsum : (k : ℝ) * (1 / N) ≤ ∑ p ∈ S, (1 : ℝ) / p := by
    rw [hk, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [hS] at hp
    obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_range] at h1
    apply one_div_le_one_div_of_le (by exact_mod_cast h2.pos)
    exact_mod_cast (by omega : p ≤ N)
  have hA : ((m : ℝ) - q) * 1.386 ≤ (m : ℝ) * Real.log 4 - q * Real.log 4 := by
    nlinarith
  have hB : ((s : ℝ) + 5) * Real.log N ≤ (t + 5) * (7.72 + t / 50) :=
    mul_le_mul (by linarith) hL hLpos.le (by positivity)
  have hkey : (N : ℝ) ≤ k * (10 * Real.log N) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htlow) ht0]
  calc 1 / (10 * Real.log N) ≤ k * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hN0]
        linarith
    _ ≤ _ := hsum

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationEqZeroOfIsAlgebraicOverPadicIntegersStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_eq_zero_of_isAlgebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ E : Derivation ℤ Ω Ω, (∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) →
    ∀ x : Ω, IsAlgZp (p := p) x → E x = 0 := by
  first | exact @GlobalTheory.K5.DerAlg.der_algZp | exact GlobalTheory.K5.DerAlg.der_algZp | (intros; apply GlobalTheory.K5.DerAlg.der_algZp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsIntStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt (p := p) (D (tr (u l * (x * v k))))) → IsInt (p := p) ((p : Ω) ^ 2 * D x) := by
  first | exact @GlobalTheory.KumDlog.der_dual_p_sq_int | exact GlobalTheory.KumDlog.der_dual_p_sq_int | (intros; apply GlobalTheory.KumDlog.der_dual_p_sq_int <;> assumption)
end

