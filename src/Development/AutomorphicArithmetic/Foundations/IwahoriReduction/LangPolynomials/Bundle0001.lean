module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.CardUn
section
noncomputable section

namespace UpperTheory.Kd.C7

private theorem mem_zpowers_un_of_primitive_root_mod_sq {l : ℕ} [Fact (Nat.Prime l)] (hl2 : l ≠ 2) (g : ℕ) (hg : ¬ l ∣ g)
    (ho : orderOf (g : ZMod l) = l - 1) (hnd : ¬ ((l : ℤ) ^ 2 ∣ (g : ℤ) ^ (l - 1) - 1))
    (r : ℕ) (x : (ZMod (l ^ r))ˣ) : x ∈ Subgroup.zpowers (un g hg r) := by
  have hp : l.Prime := Fact.out
  have hgl : (g : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hg
  have hf : (l : ℤ) ∣ (g : ℤ) ^ (l - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hgl, sub_self]
  obtain ⟨a, ha⟩ := hf
  have han : ¬ (l : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    exact hnd ⟨b, by rw [ha]; ring⟩
  have hga : (g : ℤ) ^ (l - 1) = 1 + l * a := by
    rw [← ha]; ring
  rcases r with _ | n
  · have : Subsingleton (ZMod (l ^ 0))ˣ := by
      rw [pow_zero]; infer_instance
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  set u := un g hg (n + 1) with hu
  have hcast : (u : ZMod (l ^ (n + 1))) = (g : ZMod (l ^ (n + 1))) := by
    simp [hu, un]
  have h1 : orderOf (u ^ (l - 1)) = l ^ n := by
    rw [← orderOf_units, Units.val_pow_eq_pow_val, hcast]
    have e : (g : ZMod (l ^ (n + 1))) ^ (l - 1) = 1 + (l : ZMod (l ^ (n + 1))) * (a : ZMod (l ^ (n + 1))) := by
      have := congrArg (Int.cast : ℤ → ZMod (l ^ (n + 1))) hga
      push_cast at this
      exact this
    rw [e]
    exact ZMod.orderOf_one_add_mul_prime hp hl2 a han n
  have hm : l ∣ l ^ (n + 1) := dvd_pow_self l (Nat.succ_ne_zero n)
  have h2 : l - 1 ∣ orderOf u := by
    have h3 : orderOf (ZMod.unitsMap hm u) = l - 1 := by
      rw [← orderOf_units]
      have : ((ZMod.unitsMap hm u : (ZMod l)ˣ) : ZMod l) = (g : ZMod l) := by
        simp [ZMod.unitsMap, hcast]
      rw [this, ho]
    rw [← h3]
    exact orderOf_map_dvd _ u
  have h4 : l ^ n ∣ orderOf u := h1 ▸ orderOf_pow_dvd _
  have hcard : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcop : Nat.Coprime (l ^ n) (l - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_self_sub_right hp.pos]
    simp
  have h5 : orderOf u = Nat.card (ZMod (l ^ (n + 1)))ˣ := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_natCard u
    · rw [hcard]
      exact hcop.mul_dvd_of_dvd_of_dvd h4 h2
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h5]
  rw [htop]
  exact Subgroup.mem_top x

theorem pGenEx : SGenEx := by
  intro l _ hl2
  have hp : l.Prime := Fact.out
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  have hc0 : (((c : ZMod l).val : ℕ) : ZMod l) = c := ZMod.natCast_zmod_val _
  set c0 : ℕ := (c : ZMod l).val with hc0def
  have hnd0 : ¬ l ∣ c0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff c0 l).mpr h
    rw [hc0] at h'
    exact c.ne_zero h'
  have hord : ∀ k : ℕ, orderOf ((c0 + l * k : ℕ) : ZMod l) = l - 1 := by
    intro k
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, hc0, orderOf_units, hc]
  have hndk : ∀ k : ℕ, ¬ l ∣ c0 + l * k := by
    intro k h
    exact hnd0 ((Nat.dvd_add_left (dvd_mul_right l k)).mp h)
  have hc2 : 2 ≤ c0 := by
    by_contra h
    push_neg at h
    have h01 : c0 = 0 ∨ c0 = 1 := by omega
    rcases h01 with h0 | h1
    · exact hnd0 (h0 ▸ dvd_zero l)
    · have h1' : (c : ZMod l) = 1 := by
        rw [← hc0, h1, Nat.cast_one]
      have hc1 : c = 1 := Units.ext h1'
      rw [hc1, orderOf_one] at hc
      have := hp.two_le
      omega
  by_cases hsq : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1) - 1
  · have hnd1 : ¬ ((l : ℤ) ^ 2 ∣ ((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1) := by
      intro hB
      have key := sq_dvd_add_pow_sub_sub (l : ℤ) (c0 : ℤ) (l - 1)
      have hsum : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by
        have e : (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) =
            (((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1)
              - (((c0 : ℤ) + l) ^ (l - 1) - (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ)
                - (c0 : ℤ) ^ (l - 1))
              - ((c0 : ℤ) ^ (l - 1) - 1) := by
          push_cast
          ring
        rw [e]
        exact dvd_sub (dvd_sub hB key) hsq
      have h6 : (l : ℤ) ∣ (c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ) := by
        have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [← mul_dvd_mul_iff_left hl0]
        have e2 : (l : ℤ) * ((c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ))
            = (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by ring
        rw [e2, ← sq]
        exact hsum
      have h7 : l ∣ c0 ^ (l - 1 - 1) * (l - 1) := by exact_mod_cast h6
      rcases (Nat.Prime.dvd_mul hp).mp h7 with h8 | h8
      · exact hnd0 (hp.dvd_of_dvd_pow h8)
      · have := hp.two_le
        have := Nat.le_of_dvd (by omega) h8
        omega
    exact ⟨c0 + l * 1, hndk 1, by omega, mem_zpowers_un_of_primitive_root_mod_sq hl2 _ (hndk 1) (hord 1) hnd1⟩
  · have h0 := hord 0
    simp only [mul_zero, add_zero] at h0
    exact ⟨c0, hnd0, hc2, mem_zpowers_un_of_primitive_root_mod_sq hl2 c0 hnd0 h0 hsq⟩

end UpperTheory.Kd.C7
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DlogCmp
section
noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pDlogCmp : SDlogCmp := by
  intro R _ p hp m n N hm F g w hF hg hw hL
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  set k := min n (min (j + 1 - 1) N) with hk
  have hkn : k ≤ n := by omega
  have hkj : k ≤ j := by omega
  have hkN : k ≤ N := by omega
  set D := PowerSeries.derivative (R := R) with hD
  set W := w ^ p ^ n with hW
  let J : Ideal (PowerSeries R) := Ideal.span {(p : PowerSeries R) ^ k, cyc R p (j + 1)}
  have hpow : ∀ i, k ≤ i → ∀ y : PowerSeries R, (p : PowerSeries R) ^ i * y ∈ J := by
    intro i hi y
    have e : (p : PowerSeries R) ^ i * y = (p : PowerSeries R) ^ k * ((p : PowerSeries R) ^ (i - k) * y) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    exact J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hcyc : ∀ y, cyc R p (j + 1) * y ∈ J := fun y =>
    J.mul_mem_right _ (Ideal.subset_span (by simp))
  have hev : ∀ x ∈ J, ev R p (j + 1) x ∈ Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k} := by
    intro x hx
    have hle : J ≤ (Ideal.span {((p : ℕ) : lev R p (j + 1)) ^ k}).comap (ev R p (j + 1)) := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
        exact Ideal.subset_span rfl
      · simp only [SetLike.mem_coe, Ideal.mem_comap]
        have h0 : ev R p (j + 1) (cyc R p (j + 1)) = 0 := by
          unfold ev
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [h0]
        exact Ideal.zero_mem _
    exact hle hx
  obtain ⟨a, b, hab⟩ : ∃ a b : PowerSeries R,
      F - g * W = (p : PowerSeries R) ^ N * a + cyc R p (j + 1) * b := by
    unfold LC at hL
    rw [← map_sub] at hL
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hL
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {cyc R p (j + 1)}) c
    have h0 : ev R p (j + 1) (F - g * W - (p : PowerSeries R) ^ N * a) = 0 := by
      have hea : ev R p (j + 1) a = c := by
        unfold ev
        exact ha
      rw [map_sub, ← hc, map_mul, map_pow, map_natCast, hea, mul_comm]
      exact sub_self _
    unfold ev at h0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact ⟨a, b, by linear_combination -hb⟩
  have hEJ : F - g * W ∈ J := by
    rw [hab]
    exact J.add_mem (hpow N hkN a) (hcyc b)
  have hDcyc : D (cyc R p (j + 1)) ∈ J := by
    have hc : cyc R p (j + 1) = ∑ i ∈ Finset.range p, (1 + PowerSeries.X) ^ (p ^ j * i) := by
      unfold cyc
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp.out, Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz_pow, map_add (f := _), Derivation.map_one_eq_zero, PowerSeries.derivative_X,
      zero_add, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, mul_assoc]
    exact hpow j hkj _
  have hDE : D (F - g * W) ∈ J := by
    rw [hab, map_add (f := _), Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.map_natCast]
    simp only [smul_zero, mul_zero, add_zero, smul_eq_mul]
    exact J.add_mem (hpow N hkN _) (J.add_mem (hcyc _) (J.mul_mem_left _ hDcyc))
  have hDW : D W ∈ J := by
    rw [hW, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]
    exact hpow n hkn _
  have hdd : ∀ x, dd x = (1 + PowerSeries.X) * D x := by
    intro x
    unfold dd
    rfl
  have hFi := Ring.mul_inverse_cancel F hF
  have hgi := Ring.mul_inverse_cancel g hg
  have key : dl F - dl g =
      Ring.inverse F * Ring.inverse g * ((1 + PowerSeries.X) * (D F * g - D g * F)) := by
    unfold dl
    rw [hdd F, hdd g]
    linear_combination (-(1 + PowerSeries.X) * D F * Ring.inverse F) * hgi +
      ((1 + PowerSeries.X) * D g * Ring.inverse g) * hFi
  have hmid : D F * g - D g * F = g * g * D W + g * D (F - g * W) - D g * (F - g * W) := by
    have hDF : D F = D (F - g * W) + g * D W + W * D g := by
      rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hDF]
    ring
  unfold LC
  rw [← map_sub]
  apply hev
  rw [key]
  refine J.mul_mem_left _ (J.mul_mem_left _ ?_)
  rw [hmid]
  exact J.sub_mem (J.add_mem (J.mul_mem_left _ hDW) (J.mul_mem_left _ hDE)) (J.mul_mem_left _ hEJ)

end UpperTheory.Kd.C7
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime]

private theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) ((u : c.O)).2
  have h2 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) (((u⁻¹ : c.Oˣ) : c.O)).2
  have h3 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg ((u : c.O) : PadicAlgCl l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)]

private theorem norm_pos_and_lt_one_of_irreducible (c : Coef l) (ϖ : c.O) (hϖ : Irreducible ϖ) :
    0 < ‖(ϖ : PadicAlgCl l)‖ ∧ ‖(ϖ : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hne : (ϖ : PadicAlgCl l) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  refine ⟨norm_pos_iff.2 hne, ?_⟩
  have hl : (l : c.O) ≠ 0 := by
    intro h
    apply (GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l))
    have := congrArg (fun z : c.O => (z : PadicAlgCl l)) h
    simpa using this
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ‖((l : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ e := by
    rw [he]
    push_cast
    rw [norm_mul, norm_unit c u, one_mul, norm_pow]
  have h2 : ‖((l : c.O) : PadicAlgCl l)‖ < 1 := by
    have := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)
    simpa using this
  have h3 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem ϖ.2
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [h1, h, one_pow] at h2
    exact absurd h2 (lt_irrefl 1)

private theorem dvd_of_norm_le (c : Coef l) (x y : c.O) (hy : y ≠ 0)
    (h : ‖(x : PadicAlgCl l)‖ ≤ ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  haveI := c.dvr
  by_cases hx : x = 0
  · rw [hx]
    exact dvd_zero y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨h0, h1⟩ := norm_pos_and_lt_one_of_irreducible c ϖ hϖ
  have hn : ∀ (k : ℕ) (w : c.Oˣ),
      ‖(((w : c.O) * ϖ ^ k : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ k := by
    intro k w
    push_cast
    rw [norm_mul, norm_unit c w, one_mul, norm_pow]
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨b, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [hn, hn] at h
  have hba : b ≤ a := (pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hba
  refine ⟨((v⁻¹ : c.Oˣ) : c.O) * u * ϖ ^ k, ?_⟩
  calc (u : c.O) * ϖ ^ (b + k) = ((v : c.O) * ((v⁻¹ : c.Oˣ) : c.O)) * u * ϖ ^ (b + k) := by
        rw [Units.mul_inv, one_mul]
    _ = _ := by ring

private theorem div_pow_of_cg (c : Coef l) (n : ℕ) (x : c.O) (h : Cg n (x : PadicAlgCl l) 0) :
    ∃ y : c.O, x = (l : c.O) ^ n * y := by
  have hl0 : (l : c.O) ≠ 0 := fun h0 => GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l) (by simpa using congrArg Subtype.val h0)
  refine dvd_of_norm_le c x _ (pow_ne_zero n hl0) ?_
  simpa [Cg] using h

theorem pBasEx : SBasEx := by
  intro l _ c
  haveI := c.fin
  haveI := c.dvr
  refine ⟨⟨⟨_, Module.finBasis ℤ_[l] c.O⟩⟩, fun β => ⟨fun i => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (β.e i).2,
    ?_, fun n x h => div_pow_of_cg c n x h, ?_⟩⟩
  · intro n x h i
    have hzc : ((∑ j, x j • β.e j : c.O) : PadicAlgCl l)
        = ∑ j, β.val j * algebraMap ℤ_[l] (PadicAlgCl l) (x j) := by
      simp [Bas.val, Algebra.smul_def, mul_comm]
    obtain ⟨y, hy⟩ := div_pow_of_cg c n (∑ j, x j • β.e j) (by rw [hzc]; exact h)
    have hs : (∑ j, x j • β.e j : c.O) = ((l : ℤ_[l]) ^ n) • y := by
      rw [hy, Algebra.smul_def, map_pow, map_natCast]
    have hx : β.e.repr (∑ j, x j • β.e j) i = x i := by
      rw [β.e.repr_sum_self]
    refine ⟨β.e.repr y i, ?_⟩
    rw [← hx, hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · intro x hx h1
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h1
    obtain ⟨z, hz⟩ := dvd_of_norm_le c 1 ⟨x, hx⟩
      (fun h0 => hx0 (by simpa using congrArg Subtype.val h0)) (by simp [h1])
    have hz' : (1 : PadicAlgCl l) = x * (z : PadicAlgCl l) := by
      have := congrArg Subtype.val hz
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hz'.symm]
    exact z.2

end UpperTheory.Kd.C7
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixAbs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem exists_natCast_add_mul_of_frobenius_fixed {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime]
    (σ : R ≃+* R) (hpr : Prime (p : R)) (hfrob : ∀ x : R, σ x - x ^ p ∈ Ideal.span {(p : R)})
    (x : R) (hx : σ x = x) : ∃ a : ℕ, ∃ y : R, x = a + p * y ∧ σ y = y := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (mem_nonunits_iff.mpr hpr.not_unit)
  let K := R ⧸ Ideal.span {(p : R)}
  let π : R →+* K := Ideal.Quotient.mk _
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hxx : π x ^ p = π x := by
    have h1 := hfrob x
    rw [hx] at h1
    have h2 : π (x - x ^ p) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
    rw [map_sub, map_pow] at h2
    exact (sub_eq_zero.mp h2).symm
  have hf : Function.Injective f := f.injective
  let q : Polynomial K := Polynomial.X ^ p - Polynomial.X
  have hdeg : q.natDegree = p := by
    have h1 : (Polynomial.X : Polynomial K).natDegree < (Polynomial.X ^ p : Polynomial K).natDegree := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      exact hp.out.one_lt
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, Polynomial.natDegree_X_pow]
  have hq : q ≠ 0 := by
    intro h
    have := hdeg
    rw [h, Polynomial.natDegree_zero] at this
    exact hp.out.ne_zero this.symm
  have hroot : ∀ t : K, t ^ p = t → t ∈ q.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    simp [q, ht]
  have hsub : Finset.univ.image f ⊆ q.roots.toFinset := by
    intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    apply hroot
    rw [← map_pow, ZMod.pow_card]
  have hcard : q.roots.toFinset.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ZMod.card]
    calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' q
      _ = p := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : π x ∈ Finset.univ.image f := heq ▸ hroot _ hxx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
  have hval : π (a.val : R) = π x := by
    rw [map_natCast, ZMod.natCast_val, ← ha]
    rfl
  have hmemI : x - (a.val : R) ∈ Ideal.span {(p : R)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (x - (a.val : R)) = 0
    rw [map_sub, hval, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmemI
  refine ⟨a.val, y, by rw [mul_comm, hy]; ring, ?_⟩
  have h3 : (p : R) * σ y = p * y := by
    have := congrArg σ hy
    rw [map_mul, map_natCast, map_sub, map_natCast, hx] at this
    rw [mul_comm, this, mul_comm, hy]
  exact mul_left_cancel₀ hpr.ne_zero h3

theorem UpperTheory.Kd.C7.pFixAbs :
    UpperTheory.Kd.C7.SFixAbs := by
  intro R _ p _ _ σ hσ x hx
  obtain ⟨hdom, hpr, hcomp, hfrob, -⟩ := hσ
  classical
  haveI := hdom
  haveI := hcomp
  have step : ∀ y : {y : R // σ y = y}, ∃ a : ℕ, ∃ y' : {y : R // σ y = y}, y.1 = a + p * y'.1 := by
    intro y
    obtain ⟨a, y', h1, h2⟩ := exists_natCast_add_mul_of_frobenius_fixed p σ hpr hfrob y.1 y.2
    exact ⟨a, ⟨y', h2⟩, h1⟩
  choose d nx hdn using step
  let seq : ℕ → {y : R // σ y = y} := fun n => Nat.rec ⟨x, hx⟩ (fun _ y => nx y) n
  let s : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, d (seq i) * p ^ i
  have hrep : ∀ n, x = (s n : R) + (p : R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : seq (n + 1) = nx (seq n) := rfl
      rw [ih, hdn (seq n)]
      simp only [s, Finset.sum_range_succ, e]
      push_cast
      ring
  have hdvd : ∀ m k, (p : ℤ) ^ m ∣ ((s (m + k) : ℕ) : ℤ) - (s m : ℤ) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ((s (m + (k + 1)) : ℕ) : ℤ) - s m
          = (((s (m + k)) : ℤ) - s m) + (d (seq (m + k)) : ℤ) * (p : ℤ) ^ (m + k) := by
        simp only [s, ← add_assoc, Finset.sum_range_succ]
        push_cast
        ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ (Nat.le_add_right _ _)) _)
  have hZ : ∀ (a b : ℤ_[p]) (m : ℕ), a ≡ b [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p])]
      ↔ (p : ℤ_[p]) ^ m ∣ a - b := by
    intro a b m
    rw [SModEq.sub_mem, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.smul_eq_mul,
      Ideal.mul_top, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal ℤ_[p]) inferInstance
    (f := fun n => (s n : ℤ_[p])) (by
      intro m n hmn
      rw [hZ]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have h1 := map_dvd (Int.castRingHom ℤ_[p]) (hdvd m k)
      simp only [map_pow, map_sub, map_natCast] at h1
      rw [← dvd_neg, neg_sub]
      exact h1)
  refine ⟨L, ?_⟩
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : R)})]
  intro n
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := (hZ _ _ n).mp (hL n)
  have h2 := congrArg (algebraMap ℤ_[p] R) hc
  rw [RingHom.map_sub, map_natCast, map_mul, map_pow, map_natCast] at h2
  refine ⟨-(algebraMap ℤ_[p] R c + (seq n).1), ?_⟩
  linear_combination (-1 : R) * h2 - hrep n
end

