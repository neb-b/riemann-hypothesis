module

public import Formalism.HyperbolicPlaceProducts.Bundle0001

@[expose] public section

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CardEqCardRangeNsmulMulCardKer
section
open Module

namespace Formalism.SLP.P

theorem card_eq_card_range_nsmul_mul_card_ker : Formalism.SLP.TorsionIndexEq := by
  intro A _ _ g
  set f : A →+ A := nsmulAddMonoidHom g
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

theorem card_range_nsmul_mul_card_le : Formalism.SLP.TorsionIndex := by
  intro A _ _ g K hK
  have hle : K ≤ (nsmulAddMonoidHom g : A →+ A).ker := fun x hx => by
    simpa using hK x hx
  rw [card_eq_card_range_nsmul_mul_card_ker A g]
  exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_of_le hle)

end Formalism.SLP.P
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions
section
open Module

noncomputable section

namespace Formalism.SLP.P

private theorem exists_span_singleton_eq_of_le_span_singleton {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] (v : M) (N : Submodule R M)
    (hN : N ≤ R ∙ v) : ∃ t : M, (R ∙ t) = N := by
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M v
  let I : Ideal R := N.comap f
  let J : Ideal R := LinearMap.ker f
  have hJI : J ≤ I := fun r hr => by
    show f r ∈ N
    rw [LinearMap.mem_ker.1 hr]
    exact N.zero_mem
  have key : ∃ x, J ⊔ Ideal.span {x} = I := by
    by_cases hJ : J = ⊥
    ·
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hJ
      haveI : Finite R := Finite.of_injective f hinj
      have hF : IsField R := Finite.isField_of_domain R
      by_cases hI : I = ⊥
      · exact ⟨0, by rw [hJ, hI]; simp⟩
      · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
        obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
        have hIt : I = ⊤ := (Ideal.eq_top_iff_one I).2 (by rw [← hb]; exact I.mul_mem_right b ha)
        exact ⟨1, by rw [hIt, Ideal.span_singleton_one, sup_top_eq]⟩
    · exact IsDedekindDomain.exists_sup_span_eq hJI hJ
  obtain ⟨x, hx⟩ := key
  refine ⟨x • v, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    have hxI : x ∈ I := hx ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hfx : f x ∈ N := hxI
    simpa [f] using hfx
  · intro n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 (hN hn)
    have hr : r ∈ I := by
      show f r ∈ N
      simpa [f] using hn
    rw [← hx, Submodule.mem_sup] at hr
    obtain ⟨j, hj, y, hy, rfl⟩ := hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hjv : j • v = 0 := by simpa [f] using LinearMap.mem_ker.1 hj
    rw [Submodule.mem_span_singleton]
    exact ⟨s, by rw [add_smul, hjv, zero_add, mul_smul]⟩

theorem exists_family_span_eq_of_le {R M : Type} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [Finite M] :
    ∀ (e : ℕ) (v : Fin e → M) (N : Submodule R M), N ≤ Submodule.span R (Set.range v) →
      ∃ t : Fin e → M, Submodule.span R (Set.range t) = N := by
  intro e
  induction e with
  | zero =>
    intro v N hN
    refine ⟨v, ?_⟩
    rw [Set.range_eq_empty v, Submodule.span_empty] at hN ⊢
    exact (le_bot_iff.1 hN).symm
  | succ e ih =>
    intro v N hN
    set S' : Submodule R M := Submodule.span R (Set.range (Fin.tail v)) with hS'
    have hv : Submodule.span R (Set.range v) = (R ∙ v 0) ⊔ S' := by
      conv_lhs => rw [← Fin.cons_self_tail v]
      rw [Fin.range_cons, Submodule.span_insert]
    haveI : Finite (M ⧸ S') := Finite.of_surjective _ (Submodule.mkQ_surjective S')

    have hπ : N.map S'.mkQ ≤ R ∙ S'.mkQ (v 0) := by
      rw [Submodule.map_le_iff_le_comap]
      intro n hn
      have h := hN hn
      rw [hv, Submodule.mem_sup] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 ha
      rw [Submodule.mem_comap, map_add (f := _), map_smul]
      have hb0 : S'.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero S').2 hb
      rw [hb0, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨t', ht'⟩ := exists_span_singleton_eq_of_le_span_singleton (S'.mkQ (v 0)) (N.map S'.mkQ) hπ
    have ht'm : t' ∈ N.map S'.mkQ := ht' ▸ Submodule.mem_span_singleton_self t'
    obtain ⟨n0, hn0, hn0t⟩ := ht'm
    obtain ⟨u, hu⟩ := ih (Fin.tail v) (N ⊓ S') inf_le_right
    refine ⟨Fin.cons n0 u, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, hu]
    apply le_antisymm
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hn0) inf_le_left
    · intro n hn
      have hπn : S'.mkQ n ∈ R ∙ S'.mkQ n0 := by
        rw [hn0t, ht']
        exact Submodule.mem_map_of_mem hn
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hπn
      have hd : n - r • n0 ∈ S' := by
        have h0 : S'.mkQ (n - r • n0) = 0 := by rw [map_sub, map_smul, hr, sub_self]
        exact (Submodule.Quotient.mk_eq_zero S').1 h0
      rw [Submodule.mem_sup]
      exact ⟨r • n0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), n - r • n0,
        ⟨N.sub_mem hn (N.smul_mem _ hn0), hd⟩, by abel⟩

theorem card_submodules_le_of_dedekind : Formalism.SLP.SubmoduleCountDed := by
  intro R M _ _ _ _ _ e v hv
  have hsurj : Function.Surjective
      (fun t : Fin e → M => Submodule.span R (Set.range t)) := by
    intro N
    exact exists_family_span_eq_of_le e v N (by rw [hv]; exact le_top)
  calc Nat.card (Submodule R M) ≤ Nat.card (Fin e → M) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card M ^ e := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.SLP.P

end
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DetIndexProductHyperbolicInequality
section
open Module

noncomputable section

namespace Formalism.SLP.GlobalBoundRefinements.P

open Formalism.SLP.GlobalBoundRefinements

theorem card_linearEquiv_le : Formalism.SLP.GlobalBoundRefinements.AutCount := by
  intro R M _ _ _ _ e v hv
  have hinj : Function.Injective (fun f : M ≃ₗ[R] M => fun i => f (v i)) := by
    intro f g hfg
    apply LinearEquiv.toLinearMap_injective
    exact LinearMap.ext_on_range hv (fun i => congrFun hfg i)
  calc Nat.card (M ≃ₗ[R] M) ≤ Nat.card (Fin e → M) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card M ^ e := by rw [Nat.card_fun, Nat.card_fin]


end Formalism.SLP.GlobalBoundRefinements.P
end
end

-- bundled from Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.OmegaPow
section
namespace Formalism.SLP.P

theorem two_pow_length_primeFactorsList_le (j : ℕ) (hj : 1 ≤ j) :
    2 ^ (Nat.primeFactorsList j).length ≤ j := by
  have hprod := Nat.prod_primeFactorsList (show j ≠ 0 by omega)
  calc 2 ^ (Nat.primeFactorsList j).length ≤ (Nat.primeFactorsList j).prod :=
        List.pow_card_le_prod _ _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = j := hprod

theorem pow_primeFactors_length_le : Formalism.SLP.OmegaPow := by
  intro n j hn hj
  set k := (Nat.primeFactorsList j).length
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hk : (2 : ℝ) ^ k ≤ j := by exact_mod_cast two_pow_length_primeFactorsList_le j hj

  have hklog : (k : ℝ) ≤ Real.logb 2 j := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hj0]
    simpa [Real.rpow_natCast] using hk
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

  have e1 : (n : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0,
      Real.rpow_natCast]
  have e2 : (j : ℝ) ^ Real.logb 2 n = (2 : ℝ) ^ (Real.logb 2 j * Real.logb 2 n) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hj0]
  rw [e1, e2]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hklog hlogn)

end Formalism.SLP.P
end

