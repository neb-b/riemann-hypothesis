module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_le_kmu {x : ℂ_[l]} (hx : x ∈ Rmu l) : x ∈ Kmu l := by
  have h : Rmu l ≤ (Kmu l).toSubring := by
    rw [Rmu, Subring.closure_le]
    intro z hz
    exact Subfield.subset_closure hz
  exact h hx

theorem kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := (Kmu l).le_topologicalClosure hx

theorem tch_mem_kur {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ξ ∈ MaximalUnramifiedExtension l := by
  rcases Set.mem_insert_iff.mp hξ with rfl | h
  · exact (MaximalUnramifiedExtension l).zero_mem
  · exact kmu_le_kur l (Subfield.subset_closure h)

theorem norm_sub_le_max_padic (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max x 0 y
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at h
  exact h

theorem norm_eq_of_norm_sub_lt_max {x y : ℂ_[l]} (h : ‖x - y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h1
    rw [max_eq_right hlt.le] at h
    have h2 : max ‖x‖ ‖x - y‖ < ‖y‖ := max_lt hlt h
    linarith
  · have h1 := norm_sub_le_max_padic l y (y - x)
    rw [sub_sub_cancel] at h1
    rw [max_eq_left hgt.le, norm_sub_rev] at h
    have h2 : max ‖y‖ ‖y - x‖ < ‖x‖ := max_lt hgt h
    linarith

private theorem norm_natCast_l_padicComplex_eq_inv : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p] at h
  have e : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [e] at h
  exact h

theorem norm_prime_pos_complexPadic : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime l).pos)

theorem norm_prime_lt_one_complexPadic : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime l).one_lt)

theorem kmu_discrete {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact norm_nonneg _
  obtain ⟨m, a, -, b, -, ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1 ⊢
  have hm : 1 ≤ m := by
    by_contra hc
    have hm0 : m ≤ 0 := by omega
    have := one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0
    linarith
  calc ‖(l : ℂ_[l])‖ ^ m ≤ ‖(l : ℂ_[l])‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm
    _ = ‖(l : ℂ_[l])‖ := zpow_one _

theorem exists_teichmuller_rep_mod_prime {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, r, hr, h⟩ := rmu_frob l a ha
  refine tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

theorem kmu_rep {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact ⟨0, Set.mem_insert _ _, by rw [sub_zero]; exact kmu_discrete l hx h1⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨m, a, ha', b, hb', ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1
  have hm : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · have := one_lt_zpow_of_neg₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
    · exact h
    · have := zpow_lt_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
  subst hm
  obtain ⟨α, hα, hαa⟩ := exists_teichmuller_rep_mod_prime l ha'
  obtain ⟨β, hβ, hβb⟩ := exists_teichmuller_rep_mod_prime l hb'
  have hβ1 : ‖β‖ = 1 := by
    have h2 : ‖b - β‖ < max ‖b‖ ‖β‖ :=
      lt_of_le_of_lt hβb (lt_of_lt_of_le (norm_prime_lt_one_complexPadic l) (hb ▸ le_max_left _ _))
    rw [← norm_eq_of_norm_sub_lt_max l h2, hb]
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hβ0 : β ≠ 0 := by intro h; rw [h, norm_zero] at hβ1; exact zero_ne_one hβ1
  refine ⟨α * β⁻¹, tch_mul l hα (tch_inv l hβ), ?_⟩
  have he : (l : ℂ_[l]) ^ (0 : ℤ) * (a / b) - α * β⁻¹
      = ((a - α) * β - α * (b - β)) / (b * β) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul b, hb, hβ1, mul_one, div_one]
  refine (norm_sub_le_max_padic l _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, hβ1, mul_one]; exact hαa
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (tch_norm_le l hα)).trans hβb

theorem kur_approx {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (e : ℝ) (he : 0 < e) :
    ∃ y ∈ Kmu l, ‖x - y‖ < e := by
  have hc : x ∈ closure ((Kmu l : Set ℂ_[l])) := hx
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hc e he
  exact ⟨y, hy, by rwa [dist_eq_norm] at hd⟩

theorem kur_discrete {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero]
    exact norm_nonneg _
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖x‖ hpos
  have heq : ‖x‖ = ‖y‖ := norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hxy (le_max_left _ _))
  rw [heq] at h1 ⊢
  exact kmu_discrete l hy h1

theorem kur_rep {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖(l : ℂ_[l])‖ (norm_prime_pos_complexPadic l)
  have hl1 := norm_prime_lt_one_complexPadic l
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h
    exact h.trans (max_le h1 (by linarith))
  obtain ⟨ξ, hξ, hyξ⟩ := kmu_rep l hy hy1
  refine ⟨ξ, hξ, ?_⟩
  have h := norm_sub_le_max_padic l (x - y) (ξ - y)
  rw [sub_sub_sub_cancel_right, norm_sub_rev ξ y] at h
  exact h.trans (max_le hxy.le hyξ)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem xp_zmod {p : ℕ} (hp : p.Prime) (f : PowerSeries (ZMod p)) : xp p f = f ^ p := by
  haveI := Fact.mk hp
  ext n
  have key := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q n) (PowerSeries.trunc_trunc_pow (n := n + 1) f p)
  simp only [PowerSeries.coeff_trunc, Nat.lt_add_one, ↓reduceIte] at key
  rw [← key, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← ZMod.expand_card, Polynomial.coeff_expand hp.pos]
  simp only [xp, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]
  · rfl

theorem exists_C_mul_of_map_eq_zero {p : ℕ} (h : PowerSeries ℤ)
    (h0 : h.map (Int.castRingHom (ZMod p)) = 0) :
    ∃ g : PowerSeries ℤ, h = PowerSeries.C (p : ℤ) * g := by
  have hd : ∀ n, (p : ℤ) ∣ PowerSeries.coeff n h := by
    intro n
    have h1 := congrArg (PowerSeries.coeff n) h0
    rw [PowerSeries.coeff_map, map_zero, eq_intCast] at h1
    exact (CharP.intCast_eq_zero_iff (ZMod p) p _).1 h1
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff n h / p, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hd n)]

theorem xp_congr {p : ℕ} (hp : p.Prime) (f : PowerSeries ℤ) :
    ∃ g : PowerSeries ℤ, xp p f = f ^ p + PowerSeries.C (p : ℤ) * g := by
  have hmap : (xp p f).map (Int.castRingHom (ZMod p)) = xp p (f.map (Int.castRingHom (ZMod p))) := by
    ext n
    simp only [xp, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    split_ifs <;> simp
  have h0 : (xp p f - f ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, hmap, xp_zmod hp, sub_self]
  obtain ⟨g, hg⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨g, by rw [← hg]; ring⟩

theorem sub_pow_congr {p : ℕ} (hp : p.Prime) (f g : PowerSeries ℤ) :
    ∃ w : PowerSeries ℤ, (f - g) ^ p = f ^ p - g ^ p + PowerSeries.C (p : ℤ) * w := by
  haveI := Fact.mk hp
  haveI : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (PowerSeries (ZMod p))).injective p
  have h0 : ((f - g) ^ p - (f ^ p - g ^ p)).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, map_sub, map_sub, map_pow, map_pow, sub_pow_char, sub_self]
  obtain ⟨w, hw⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨w, by rw [← hw]; ring⟩

theorem rescale_congr {p : ℕ} (hp : 0 < p) (b : ℕ) (f : PowerSeries ℤ) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧
      PowerSeries.rescale (zetaC p ^ b) (f.map (Int.castRingHom ℂ)) =
        f.map (Int.castRingHom ℂ) + PowerSeries.C (1 - zetaC p) * w := by
  refine ⟨PowerSeries.mk fun n => -(∑ i ∈ Finset.range (b * n), zetaC p ^ i) * ((PowerSeries.coeff n f : ℤ) : ℂ), ?_, ?_⟩
  · intro n
    rw [PowerSeries.coeff_mk]
    exact mul_mem (neg_mem (sum_mem fun i _ => pow_mem (Subring.subset_closure (Set.mem_singleton _)) _))
      (intCast_mem _ _)
  · ext n
    simp only [map_add (f := _), PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, eq_intCast]
    have hg := geom_sum_mul (zetaC p) (b * n)
    linear_combination (-((PowerSeries.coeff n f : ℤ) : ℂ)) * hg

theorem zetaC_isPrimitiveRoot {p : ℕ} (hp : p ≠ 0) : IsPrimitiveRoot (zetaC p) p := Complex.isPrimitiveRoot_exp p hp

theorem p_mem_span {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (p : ℂ) = (1 - zetaC p) * r := by
  haveI := Fact.mk hp
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hmem : ∀ μ ∈ primitiveRoots p ℂ, μ ∈ Rm p := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) _
  have hprod : (p : ℂ) = ∏ μ ∈ primitiveRoots p ℂ, (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := ℂ) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
    simpa using h1.symm
  refine ⟨∏ μ ∈ (primitiveRoots p ℂ).erase (zetaC p), (1 - μ),
    prod_mem fun μ hμ => sub_mem (one_mem _) (hmem μ (Finset.mem_of_mem_erase hμ)), ?_⟩
  rw [hprod, Finset.mul_prod_erase _ _ ((mem_primitiveRoots hp.pos).2 hζ)]

theorem one_sub_zeta_pow {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (1 - zetaC p) ^ p = (p : ℂ) * r := by
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hz : zetaC p ∈ Rm p := Subring.subset_closure (Set.mem_singleton _)
  set z : Rm p := ⟨zetaC p, hz⟩ with hzdef
  have hzc : (z : ℂ) = zetaC p := rfl
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Rm p) (-z)
  have hr' : (1 - zetaC p) ^ p = 1 + (-zetaC p) ^ p + p * (-(zetaC p * (r : ℂ))) := by
    have h1 := congrArg (fun x : Rm p => (x : ℂ)) hr
    push_cast at h1
    rw [hzc] at h1
    rw [sub_eq_add_neg, h1]
    ring
  have hm : -(zetaC p * (r : ℂ)) ∈ Rm p := neg_mem (mul_mem hz r.2)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · refine ⟨1 + -(zetaC 2 * (r : ℂ)), add_mem (one_mem _) hm, ?_⟩
    rw [hr', neg_sq, hζ.pow_eq_one]
    push_cast
    ring
  · refine ⟨-(zetaC p * (r : ℂ)), hm, ?_⟩
    rw [hr', hodd.neg_pow, hζ.pow_eq_one]
    ring

theorem one_sub_zeta_ne_zero {p : ℕ} (hp : p.Prime) : 1 - zetaC p ≠ 0 := by
  exact sub_ne_zero.2 ((zetaC_isPrimitiveRoot hp.ne_zero).ne_one hp.one_lt).symm

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocC
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_padicAlgCl {l : ℕ} [Fact l.Prime] {z : ℂ_[l]} (hz : IsAlgebraic ℚ_[l] z) :
    ∃ y : PadicAlgCl l, algebraMap (PadicAlgCl l) ℂ_[l] y = z := by

  have hsplit : ((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).Splits :=
    IsAlgClosed.splits _
  have hne : (minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hz.isIntegral)
  have hroot : (((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).map
      (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot z := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact (Polynomial.eval_map_algebraMap _ _).trans (minpoly.aeval _ _)
  obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot hne hroot
  exact ⟨y, hy⟩

theorem isAlgebraic_padic_map {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {x : ℂ}
    (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ_[l] (ι x) := by
  have h : IsAlgebraic ℚ (ι x) := hx.algHom (ι : ℂ →+* ℂ_[l]).toRatAlgHom
  exact h.tower_top ℚ_[l]

theorem locEmb (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) :
    ∃ e : Om d →+* PadicAlgCl l, ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ) := by
  set j : PadicAlgCl l →+* ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] with hj

  let J : PadicAlgCl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => j.injective (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  have hmem : ∀ x : Om d, (ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ) x ∈ j.range := by
    intro x
    obtain ⟨y, hy⟩ := exists_padicAlgCl (isAlgebraic_padic_map ι (Om_isAlgebraic d x))
    exact ⟨y, hy⟩
  refine ⟨J.symm.toRingHom.comp (((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ)).codRestrict j.range hmem),
    fun x => ?_⟩
  have h := congrArg Subtype.val (J.apply_symm_apply
    ((((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ)).codRestrict j.range hmem) x))
  exact h

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocD
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_of_ratRoot {Ω M : Type*} [Field Ω] [IsAlgClosed Ω] [Field M] (e : Ω →+* M)
    (f₀ : ℚ →+* Ω) (f : ℚ →+* M) {p : Polynomial ℚ} (hp : p ≠ 0) {y : M}
    (hy : p.eval₂ f y = 0) : ∃ a : Ω, e a = y := by
  have hP : p.map f₀ ≠ 0 := (Polynomial.map_ne_zero_iff f₀.injective).2 hp
  have hr : ((p.map f₀).map e).roots = (p.map f₀).roots.map e :=
    (IsAlgClosed.splits _).roots_map e
  have hf : e.comp f₀ = f := Subsingleton.elim _ _
  have hmem : y ∈ ((p.map f₀).map e).roots := by
    rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff e.injective).2 hP), Polynomial.map_map, hf,
      Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hy
  rw [hr, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_e_eq {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (r : PadicAlgCl l →+* PadicAlgCl l) (x : Om d) : ∃ y : Om d, e y = r (e x) := by
  obtain ⟨p, hp, hpx⟩ := Om_isAlgebraic d x
  have : IsAlgClosed (Om d) :=
    (IsAlgClosed.algebraicClosure_eq_bot_iff (Om d) ℂ).mp (algebraicClosure.algebraicClosure_eq_bot (KQ d) ℂ)
  let f₀ : ℚ →+* Om d := algebraMap ℚ (Om d)
  have h0 : p.eval₂ f₀ x = 0 := by
    apply (algebraMap (Om d) ℂ).injective
    rw [Polynomial.hom_eval₂, map_zero]
    have : (algebraMap (Om d) ℂ).comp f₀ = algebraMap ℚ ℂ := Subsingleton.elim _ _
    rw [this]
    exact hpx
  refine exists_of_ratRoot e f₀ ((r.comp e).comp f₀) hp ?_
  have := congrArg (r.comp e) h0
  rw [Polynomial.hom_eval₂, map_zero] at this
  exact this

theorem norm_lt_of_res {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ < 1) : ‖r z‖ < 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact lt_of_le_of_lt h (max_lt (hr z hz.le) hz)

theorem norm_le_of_res {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : ‖r z‖ ≤ 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact le_trans h (max_le (hr z hz).le hz)

theorem norm_le_iff_of_res {l : ℕ} [Fact l.Prime] (r : PadicAlgCl l →+* PadicAlgCl l)
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) (z : PadicAlgCl l) : ‖r z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  refine ⟨fun h => ?_, fun h => norm_le_of_res hr h⟩
  by_contra hz
  push Not at hz
  have h1 : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have h2 := norm_lt_of_res hr h1
  rw [map_inv₀, norm_inv] at h2
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    linarith
  have h3 : 0 < ‖r z‖ := norm_pos_iff.2 ((map_ne_zero r).2 hz0)
  have h4 : 1 ≤ ‖r z‖⁻¹ := (one_le_inv₀ h3).2 h
  linarith

theorem fix_KQ {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (k : KQ d) : ρ (e (algebraMap (KQ d) (Om d) k)) = e (algebraMap (KQ d) (Om d) k) := by
  let φ₁ : KQ d →ₐ[ℚ] PadicAlgCl l := (e.comp (algebraMap (KQ d) (Om d))).toRatAlgHom
  let φ₂ : KQ d →ₐ[ℚ] PadicAlgCl l :=
    ((ρ : PadicAlgCl l →+* PadicAlgCl l).comp (e.comp (algebraMap (KQ d) (Om d)))).toRatAlgHom
  have h : φ₂ = φ₁ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (s := {sqD d}) rfl ?_
    intro x hx
    have hx' : x = sqD d := hx
    subst hx'
    have hm : e (algebraMap (KQ d) (Om d) (sqK d)) ∈
        IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    exact ρ.commutes ⟨_, hm⟩
  exact DFunLike.congr_fun h k

theorem locLift {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (e : Om d →+* PadicAlgCl l)
    (he : ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ))
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (hρ : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) :
    ∃ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ ∧ ∀ x : Om d, e (σ x) = ρ (e x) := by
  have hinj : Function.Injective e := e.injective
  choose g hg using exists_e_eq e (ρ : PadicAlgCl l →+* PadicAlgCl l)
  choose g' hg' using exists_e_eq e (ρ.symm : PadicAlgCl l →+* PadicAlgCl l)
  have hg1 : ∀ x, e (g x) = ρ (e x) := hg
  have hg2 : ∀ x, e (g' x) = ρ.symm (e x) := hg'
  let σ : Om d ≃ₐ[KQ d] Om d :=
    { toFun := g
      invFun := g'
      left_inv := fun x => hinj (by rw [hg2, hg1, AlgEquiv.symm_apply_apply])
      right_inv := fun x => hinj (by rw [hg1, hg2, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => hinj (by rw [hg1, map_mul, map_mul, map_mul, hg1, hg1])
      map_add' := fun x y => hinj (by rw [hg1, map_add (f := _), map_add (f := _), map_add (f := _), hg1, hg1])
      commutes' := fun k => hinj (by rw [hg1, fix_KQ]) }
  have hσ : ∀ x, e (σ x) = ρ (e x) := hg1
  have hn : ∀ x : Om d, ‖ι (x : ℂ)‖ = ‖e x‖ := fun x => by
    rw [← he, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  have hiff : ∀ x : Om d, σ x ∈ Aio d l ι ↔ x ∈ Aio d l ι := fun x => by
    rw [mem_Aio, mem_Aio, hn, hn, hσ]
    exact norm_le_iff_of_res (ρ : PadicAlgCl l →+* PadicAlgCl l) hρ (e x)
  refine ⟨σ, ⟨?_, ?_⟩, hσ⟩
  · show σ • Aio d l ι = Aio d l ι
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hiff]
    have : σ (σ⁻¹ • x) = x := σ.apply_symm_apply x
    rw [this]
  · intro x hx
    rw [mem_nonunits_Aio]
    rw [hn, map_sub, hσ]
    exact hρ _ (by rw [← hn]; exact (mem_Aio ι x).1 hx)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPerm
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem perm_Tmat_det {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : (Tmat t).det = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  simp only [Tmat, Matrix.det_fin_two_of, mul_zero, sub_zero]
  exact_mod_cast Nat.mul_div_cancel' hdvd

end ReciprocityTheory.ChartRestriction.L1
end
end

