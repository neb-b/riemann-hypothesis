module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassA
section
namespace KStar.IdealCounting

open Finset

private theorem card_fiber_le (n M k : ℕ) (hk : 1 ≤ k) :
    (((Fintype.piFinset fun _ : Fin (n + 2) => Icc 1 M).filter
      (fun a => ∏ i, a i ≤ M)).filter (fun a => a 0 = k)).card ≤
    ((Fintype.piFinset fun _ : Fin (n + 1) => Icc 1 (M / k)).filter
      (fun a => ∏ i, a i ≤ M / k)).card := by
  refine Finset.card_le_card_of_injOn (fun a => Fin.tail a) ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    rw [Fin.prod_univ_succ, h3] at h2
    have h4 : ∏ i, Fin.tail a i ≤ M / k := by
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact h2
    refine ⟨fun i => ⟨(h1 _).1, le_trans ?_ h4⟩, h4⟩
    exact Finset.single_le_prod' (f := fun i => Fin.tail a i) (fun j _ => (h1 _).1) (mem_univ i)
  · intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    have : Fin.tail a = Fin.tail b := hab
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, ha.2, hb.2, this]

theorem card_tuples_le (n M : ℕ) (hM : 1 ≤ M) :
    (((Fintype.piFinset fun _ : Fin (n + 1) => Icc 1 M).filter
      (fun a => ∏ i, a i ≤ M)).card : ℝ) ≤ M * (1 + Real.log M) ^ n := by
  induction n generalizing M with
  | zero =>
    have := Finset.card_filter_le (Fintype.piFinset fun _ : Fin (0 + 1) => Icc 1 M)
      (fun a => ∏ i, a i ≤ M)
    rw [Fintype.card_piFinset] at this
    simp only [Nat.card_Icc, Nat.add_sub_cancel, prod_const, card_univ, Fintype.card_fin,
      zero_add, pow_one] at this
    rw [pow_zero, mul_one]
    exact_mod_cast this
  | succ n ih =>
    have hlog : 0 ≤ Real.log M := Real.log_natCast_nonneg M
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin (n + 1 + 1) → ℕ => a 0)
      (t := Icc 1 M) (by
        intro a ha
        simp only [coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at ha
        exact_mod_cast ha.1 0)]
    push_cast
    have key : ∀ k ∈ Icc 1 M,
        ((((Fintype.piFinset fun _ : Fin (n + 1 + 1) => Icc 1 M).filter
          (fun a => ∏ i, a i ≤ M)).filter (fun a => a 0 = k)).card : ℝ) ≤
          (M * (1 + Real.log M) ^ n) * ((k : ℝ))⁻¹ := by
      intro k hk
      rw [mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
      have h1 : 1 ≤ M / k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have h2 := ih (M / k) h1
      have h3 := card_fiber_le n M k hk.1
      have h4 : ((M / k : ℕ) : ℝ) ≤ M * (k : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv]; exact Nat.cast_div_le
      have h5 : Real.log ((M / k : ℕ) : ℝ) ≤ Real.log M := by
        apply Real.log_le_log (by exact_mod_cast h1)
        exact_mod_cast Nat.div_le_self M k
      have h6 : 0 ≤ Real.log ((M / k : ℕ) : ℝ) := Real.log_natCast_nonneg _
      calc _ ≤ _ := Nat.cast_le.2 h3
        _ ≤ _ := h2
        _ ≤ (M * (k : ℝ)⁻¹) * (1 + Real.log M) ^ n := by gcongr
        _ = _ := by ring
    have hh : ∑ k ∈ Icc 1 M, ((k : ℝ))⁻¹ ≤ 1 + Real.log M := by
      have := harmonic_le_one_add_log M
      rw [harmonic_eq_sum_Icc] at this
      push_cast at this
      exact this
    calc _ ≤ _ := Finset.sum_le_sum key
      _ = (M * (1 + Real.log M) ^ n) * ∑ k ∈ Icc 1 M, ((k : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (M * (1 + Real.log M) ^ n) * (1 + Real.log M) := by gcongr
      _ = _ := by ring

end KStar.IdealCounting
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassB
section
namespace KStar.IdealCounting

open Finset NumberField

private theorem classB_prod {ι : Type*} {n : ℕ} (q : ι → ℕ) (idx : ι → Fin n) (s : Multiset ι) :
    ∏ i, ((s.filter (fun x => idx x = i)).map q).prod = (s.map q).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h : ∀ i, (((a ::ₘ s).filter (fun x => idx x = i)).map q).prod =
        (if idx a = i then q a else 1) * ((s.filter (fun x => idx x = i)).map q).prod := by
      intro i
      by_cases h : idx a = i
      · simp [Multiset.filter_cons_of_pos, h]
      · simp [Multiset.filter_cons_of_neg, h]
    simp only [h, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Multiset.map_cons, Multiset.prod_cons]

private theorem classB_inj {ι : Type*} {n : ℕ} (q : ι → ℕ) (idx : ι → Fin n)
    (hq : ∀ x, (q x).Prime) (hinj : ∀ x y, q x = q y → idx x = idx y → x = y)
    (s t : Multiset ι)
    (h : ∀ i, ((s.filter (fun x => idx x = i)).map q).prod =
      ((t.filter (fun x => idx x = i)).map q).prod) : s = t := by
  classical
  have h1 : ∀ (u : Multiset ι), UniqueFactorizationMonoid.normalizedFactors (u.map q).prod
      = u.map q := by
    intro u
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro p hp
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hp
    exact (hq x).prime
  have h2 : ∀ i, (s.filter (fun x => idx x = i)).map q = (t.filter (fun x => idx x = i)).map q := by
    intro i
    rw [← h1, h i, h1]
  have hg : Function.Injective (fun x => (idx x, q x)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hinj x y hxy.2 hxy.1
  have h3 : ∀ (u : Multiset ι) i, (u.filter (fun x => idx x = i)).map (fun x => (idx x, q x)) =
      ((u.filter (fun x => idx x = i)).map q).map (fun r => (i, r)) := by
    intro u i
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x hx
    simp [(Multiset.mem_filter.mp hx).2]
  have h4 : ∀ i, s.filter (fun x => idx x = i) = t.filter (fun x => idx x = i) := by
    intro i
    apply Multiset.map_injective hg
    rw [h3, h3, h2]
  ext x
  have := congrArg (Multiset.count x) (h4 (idx x))
  rwa [Multiset.count_filter_of_pos (by rfl), Multiset.count_filter_of_pos (by rfl)] at this

private theorem classB_idx {ι : Type*} {n : ℕ} (q : ι → ℕ)
    (h : ∀ p, ∃ S : Finset ι, S.card ≤ n ∧ ∀ x, q x = p → x ∈ S) :
    ∃ idx : ι → Fin n, ∀ x y, q x = q y → idx x = idx y → x = y := by
  choose S hS hS' using h
  have : ∀ p, ∃ f : S p → Fin n, Function.Injective f := by
    intro p
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := S p) (β := Fin n)
      (by simpa using hS p)
    exact ⟨f, f.injective⟩
  choose f hf using this
  refine ⟨fun x => f (q x) ⟨x, hS' _ x rfl⟩, ?_⟩
  intro x y hxy hi
  have key : ∀ p (hp : q y = p), f (q y) ⟨y, hS' _ y rfl⟩ = f p ⟨y, hS' _ y hp⟩ := by
    rintro p rfl; rfl
  simp only at hi
  rw [key (q x) hxy.symm] at hi
  exact congrArg Subtype.val (hf _ hi)

open IsDedekindDomain in
private theorem classB_fact (K : Type*) [Field K] [NumberField K] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ s : Multiset (HeightOneSpectrum (𝓞 K)), (s.map (fun v => v.asIdeal)).prod = I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => exact ⟨0, by simpa using (isUnit_iff_eq_one.mp hx).symm⟩
  | h₃ a p ha hp ih =>
    obtain ⟨s, hs⟩ := ih ha
    exact ⟨⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ ::ₘ s, by simp [hs]⟩

theorem card_ideals_le_tuples (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      ((Fintype.piFinset fun _ : Fin (Module.finrank ℚ K) => Icc 1 M).filter
        (fun a => ∏ i, a i ≤ M)).card := by
  classical
  let q : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => Ideal.absNorm (v.asIdeal.under ℤ)
  have hq : ∀ v, (q v).Prime := by
    intro v
    have := v.isPrime
    have : NeZero v.asIdeal := ⟨v.ne_bot⟩
    exact Nat.absNorm_under_prime v.asIdeal
  have hle : ∀ v, q v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Int.absNorm_under_dvd_absNorm v.asIdeal)
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨idx, hidx⟩ := classB_idx (n := Module.finrank ℚ K) q (by
    intro p
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      refine ⟨(IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).preimage
        (fun v => v.asIdeal) (fun a _ b _ h => IsDedekindDomain.HeightOneSpectrum.ext h), ?_, ?_⟩
      · refine le_trans ?_ (Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K h0)
        apply Finset.card_le_card_of_injOn (fun v => v.asIdeal)
        · intro v hv
          exact Finset.mem_coe.mpr (Finset.mem_preimage.mp (Finset.mem_coe.mp hv))
        · exact fun a _ b _ h => IsDedekindDomain.HeightOneSpectrum.ext h
      · rintro v rfl
        refine Finset.mem_preimage.mpr ((IsDedekindDomain.mem_primesOverFinset_iff h0 _).mpr ?_)
        exact ⟨v.isPrime, Int.liesOver_span_absNorm v.asIdeal⟩
    · exact ⟨∅, by simp, fun x hx => absurd (hx ▸ hq x) hp⟩)
  choose s hs using classB_fact K
  rw [← Nat.card_eq_finsetCard]
  have hprod : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), ((s I hI).map q).prod ≤ Ideal.absNorm I := by
    intro I hI
    conv_rhs => rw [← hs I hI, map_multiset_prod, Multiset.map_map]
    exact Multiset.prod_map_le_prod_map _ _ (fun v _ => hle v)
  have hpos : ∀ u : Multiset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)), 0 < (u.map q).prod := by
    intro u
    apply Multiset.prod_pos
    intro a ha
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (hq x).pos
  refine Nat.card_le_card_of_injective
    (fun I => ⟨fun i => (((s I.1 I.2.1).filter (fun x => idx x = i)).map q).prod, ?_⟩) ?_
  · have h1 := (classB_prod q idx (s I.1 I.2.1)).trans_le ((hprod I.1 I.2.1).trans I.2.2)
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨hpos _, le_trans ?_ h1⟩, h1⟩
    exact Finset.single_le_prod' (f := fun i => (((s I.1 I.2.1).filter
      (fun x => idx x = i)).map q).prod) (fun j _ => hpos _) (Finset.mem_univ i)
  · intro I J hIJ
    have h := classB_inj q idx hq hidx _ _ (congrFun (congrArg Subtype.val hIJ))
    apply Subtype.ext
    rw [← hs I.1 I.2.1, ← hs J.1 J.2.1, h]

end KStar.IdealCounting
end

