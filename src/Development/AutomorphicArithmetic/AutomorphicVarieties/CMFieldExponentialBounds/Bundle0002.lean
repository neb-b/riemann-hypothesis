module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.layerex
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V
open Polynomial

private theorem layerex_up {K : Type} [Field K] {l m : ℕ} (hl : l.Prime) {b : K}
    (h : IsPrimitiveRoot (b ^ l) (l ^ (m + 1))) : IsPrimitiveRoot b (l ^ (m + 2)) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : ¬ b ^ (l ^ (m + 1)) = 1 := by
    intro e
    have : (b ^ l) ^ (l ^ m) = 1 := by rw [← pow_mul, ← pow_succ']; exact e
    exact h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
      (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self m)) this
  have h2 : b ^ (l ^ (m + 1 + 1)) = 1 := by
    rw [pow_succ' l (m + 1), pow_mul]; exact h.pow_eq_one
  have h3 := orderOf_eq_prime_pow h1 h2
  have := IsPrimitiveRoot.orderOf b
  rwa [h3] at this

private theorem layerex_max (K : Type) [Field K] [NumberField K] {l k : ℕ} (hl : l.Prime)
    (h : ∃ z : K, IsPrimitiveRoot z (l ^ (k + 1))) :
    ∃ m, k ≤ m ∧ (∃ z : K, IsPrimitiveRoot z (l ^ (m + 1))) ∧
      ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2)) := by
  by_contra hc
  push Not at hc
  have key : ∀ n, ∃ z : K, IsPrimitiveRoot z (l ^ (k + n + 1)) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact hc (k + n) (by omega) ih
  obtain ⟨z, hz⟩ := key (Module.finrank ℚ K)
  have hpos : 0 < Nat.lcm (l ^ (k + Module.finrank ℚ K + 1)) (l ^ (k + Module.finrank ℚ K + 1)) := by
    rw [Nat.lcm_self]; exact pow_pos hl.pos _
  have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz (Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hl] at h1
  have h2 : k + Module.finrank ℚ K < l ^ (k + Module.finrank ℚ K) := Nat.lt_pow_self hl.one_lt
  have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
  have h4 := Nat.mul_le_mul_left (l ^ (k + Module.finrank ℚ K)) h3
  omega

private theorem layerex_step (K : Type) [Field K] [NumberField K] {l m : ℕ} (hl : l.Prime)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (m + 1))) (hn : ¬ ∃ z : K, IsPrimitiveRoot z (l ^ (m + 2))) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K'),
      IsCyclotomicExtension {l ^ (m + 2)} K K' ∧ Module.finrank K K' = l := by
  have hirr : Irreducible (X ^ l - C z : K[X]) :=
    X_pow_sub_C_irreducible_of_prime hl (fun b hb => hn ⟨b, layerex_up hl (hb ▸ hz)⟩)
  haveI : Fact (Irreducible (X ^ l - C z : K[X])) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ l - C z : K[X])) := pb.finite
  haveI : NeZero (l ^ (m + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root (X ^ l - C z : K[X])) (l ^ (m + 2)) := by
    apply layerex_up hl
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of (X ^ l - C z : K[X])).injective
  refine ⟨AdjoinRoot (X ^ l - C z : K[X]), inferInstance, NumberField.of_module_finite K _, inferInstance, ?_, ?_⟩
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have : x ∈ Algebra.adjoin K {AdjoinRoot.root (X ^ l - C z : K[X])} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_mono ?_ this
    rintro _ rfl
    exact hr.pow_eq_one
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]

theorem UpperTheory.V.exists_cyclotomic_layer_of_primitiveRoot :
    ∀ (l j : ℕ), l.Prime → l ≠ 2 → ∀ (L : Type) [Field L] [NumberField L], (∃ z : L, IsPrimitiveRoot z l) →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'), IsLayer l j L L' := by
  intro l j hl _ L _ _ hz
  have key : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L'),
      (∃ k : ℕ, IsCyclotomicExtension {l ^ (k + 1)} L L') ∧ Module.finrank L L' = l ^ j := by
    induction j with
    | zero =>
      refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨0, ?_⟩, by simp⟩
      haveI : NeZero (l ^ (0 + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hz, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, ⟨k, hk⟩, hd⟩ := ih
      obtain ⟨m, hkm, ⟨z, hz⟩, hn⟩ := layerex_max K (k := k) hl
        (hk.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hl.ne_zero))
      obtain ⟨K', _, _, _, hc, hd'⟩ := layerex_step K hl hz hn
      letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
      haveI : IsScalarTower L K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine ⟨K', inferInstance, inferInstance, inferInstance, ⟨m + 1, ?_⟩, ?_⟩
      · haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
        have h1 := IsCyclotomicExtension.trans {l ^ (k + 1)} {l ^ (m + 2)} L K K' (algebraMap K K').injective
        rw [Set.union_comm] at h1
        exact (IsCyclotomicExtension.iff_union_of_dvd L K'
          ⟨l ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hl.ne_zero, pow_dvd_pow _ (by omega)⟩).2 h1
      · rw [← Module.finrank_mul_finrank L K K', hd, hd', pow_succ]
  obtain ⟨L', _, _, _, ⟨k, hk⟩, hd⟩ := key
  exact ⟨L', inferInstance, inferInstance, inferInstance, ⟨k + 1, hk⟩, hd⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.logpair
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.log_mul_le_rpow_of_winPair :
    ∀ eps : ℝ, 0 < eps → ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∀ q d : ℕ, WinPair eps Y q d → Real.log ((q : ℝ) * d) ≤ Y ^ (eps / 4) := by
  intro eps heps
  have hs : 0 < eps / 20 := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop 2 hs).bound (by norm_num : (0:ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop hs).eventually_ge_atTop 2
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_gt_atTop 0))
  refine ⟨Y0, fun Y hY q d hw => ?_⟩
  obtain ⟨⟨hl, hg⟩, hpos⟩ := hY0 Y hY
  have hq : (0:ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd : (0:ℝ) < d := by exact_mod_cast hw.d_prime.pos
  rw [Real.log_mul hq.ne' hd.ne']
  have hA : 0 < Y ^ (eps / 5) := Real.rpow_pos_of_pos hpos _
  have hB : 0 < Y ^ (eps / 20) := Real.rpow_pos_of_pos hpos _
  rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_pos hB] at hl
  have hsplit : Y ^ (eps / 4) = Y ^ (eps / 5) * Y ^ (eps / 20) := by
    rw [← Real.rpow_add hpos]
    ring_nf
  rw [hsplit]
  have hq' := hw.q_up
  have hd' := hw.d_up
  nlinarith [mul_le_mul_of_nonneg_left hl hA.le, mul_le_mul_of_nonneg_left hg hA.le]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.minusle
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.minusBound_le_exp_of_log_le :
    ∀ (C : ℝ) (o : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (n N t : ℕ) (W : ℝ), 1 ≤ N → 1 ≤ t → n ≤ N → Real.log ((N : ℝ) * t) ≤ 2 * W →
      minusBound C o n N t ≤ K * Real.exp (8 * W) := by
  intro C o
  refine ⟨3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3, by positivity, ?_⟩
  intro n N t W hN ht hn hW
  unfold minusBound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * t := one_le_mul_of_one_le_of_one_le hN1 ht1
  have hXpos : 0 < (N : ℝ) * t := by linarith
  have hXe : (N : ℝ) * t ≤ Real.exp (2 * W) := by
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr hW
  have hX4 : ((N : ℝ) * t) ^ 4 ≤ Real.exp (8 * W) := by
    have e : Real.exp (8 * W) = Real.exp (2 * W) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hXpos.le hXe 4
  have hnt : (n : ℝ) * t ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_right hn' (by positivity)
  have htX : (t : ℝ) ≤ (N : ℝ) * t := by nlinarith
  have hlog : Real.log ((t : ℝ) * N) ≤ (N : ℝ) * t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * N by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((t : ℝ) * N) := Real.log_nonneg (by linarith)
  have h1 : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) ≤ 3 * ((N : ℝ) * t) ^ 4 := by
    have h3 : (n : ℝ) * t * t * Real.log (t * N) ≤ ((N : ℝ) * t) ^ 3 := by
      calc (n : ℝ) * t * t * Real.log (t * N)
          ≤ ((N : ℝ) * t) * ((N : ℝ) * t) * ((N : ℝ) * t) :=
            mul_le_mul (mul_le_mul hnt htX (by positivity) (by positivity)) hlog hlog0 (by positivity)
        _ = ((N : ℝ) * t) ^ 3 := by ring
    have h34 : ((N : ℝ) * t) ^ 3 ≤ ((N : ℝ) * t) ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
    have e : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) = 3 * ((n : ℝ) * t * t * Real.log (t * N)) := by ring
    rw [e]
    linarith
  have h2 : ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ (∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hl1 : (1 : ℝ) ≤ l := by
      have := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
      exact_mod_cast this.one_lt.le
    have hge : (1 : ℝ) ≤ t * l * N :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht1 hl1) hN1
    have hlg : Real.log ((t : ℝ) * l * N) ≤ l * ((N : ℝ) * t) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * l * N by linarith)
      linarith
    have hlg0 : 0 ≤ Real.log ((t : ℝ) * l * N) := Real.log_nonneg hge
    have hsq : Real.log ((t : ℝ) * l * N) ^ 2 ≤ (l * ((N : ℝ) * t)) ^ 2 := pow_le_pow_left₀ hlg0 hlg 2
    have hnt2 : ((n : ℝ) * t) ^ 2 ≤ ((N : ℝ) * t) ^ 2 := pow_le_pow_left₀ (by positivity) hnt 2
    calc (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
        = (l : ℝ) * ((n : ℝ) * t) ^ 2 * Real.log (t * l * N) ^ 2 := by ring
      _ ≤ (l : ℝ) * ((N : ℝ) * t) ^ 2 * (l * ((N : ℝ) * t)) ^ 2 := by gcongr
      _ = (l : ℝ) ^ 3 * ((N : ℝ) * t) ^ 4 := by ring
  have hS0 : 0 ≤ ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2 :=
    Finset.sum_nonneg (fun l _ => by positivity)
  have hK0 : 0 ≤ 3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3 := by positivity
  calc 3 * (n : ℝ) * t ^ 2 * Real.log (t * N)
        + C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ 3 * ((N : ℝ) * t) ^ 4 + |C| * ((∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4) :=
        add_le_add h1 ((mul_le_mul_of_nonneg_right (le_abs_self C) hS0).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    _ = (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by ring
    _ ≤ (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * Real.exp (8 * W) :=
        mul_le_mul_of_nonneg_left hX4 hK0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.primesex
section
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

open Polynomial in
private theorem finrank_quadratic_splitting_field (p : ℕ) (hp : 0 < p) (L : Type) [Field L] [Algebra ℚ L]
    [h : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Module.finrank ℚ L = 2 := by
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hdeg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hnoroot : ∀ x : ℚ, ¬ f.IsRoot x := by
    intro x hx
    rw [hf] at hx
    simp [Polynomial.IsRoot] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible f :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hnoroot
  have hspl := IsSplittingField.splits L f
  have hdeg0 : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]
    decide
  obtain ⟨α, hα⟩ := hspl.exists_eval_eq_zero hdeg0
  have haeval : aeval α f = 0 := by
    rw [aeval_def, ← eval_map]
    exact hα
  have hmin : f = minpoly ℚ α := minpoly.eq_of_irreducible_of_monic hirr haeval hmon
  have hint : IsIntegral ℚ α := ⟨f, hmon, by rw [← aeval_def]; exact haeval⟩
  have hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  have htop : IntermediateField.adjoin ℚ {α} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin ℚ (f.rootSet L) := by
      rw [IsSplittingField.adjoin_rootSet L f]
      trivial
    have hle : Algebra.adjoin ℚ (f.rootSet L) ≤ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by
      apply Algebra.adjoin_le
      intro β hβ
      rw [Polynomial.mem_rootSet] at hβ
      have e1 := hβ.2
      have e2 := haeval
      rw [hf] at e1 e2
      simp at e1 e2
      have : (β - α) * (β + α) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp this with h | h
      · have hb : β = α := by linear_combination h
        rw [hb]
        exact IntermediateField.mem_adjoin_simple_self ℚ α
      · have hb : β = -α := by linear_combination h
        rw [hb]
        exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ α)
    exact hle hy
  rw [← IntermediateField.finrank_top', ← htop, hfin]

open Polynomial in
private theorem finrank_kstar (p : ℕ) (hp : 0 < p) : Module.finrank ℚ (Kstar p) = 2 := by
  show Module.finrank ℚ (SplittingField (X ^ 2 + C (p : ℚ))) = 2
  exact @finrank_quadratic_splitting_field p hp _ _ _ (Polynomial.IsSplittingField.splittingField _)

theorem UpperTheory.V.pK_pOne_prime_conditions :
    ∀ ψ : PChar, ((pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N) ∧
      ((pOne ψ).Prime ∧ pOne ψ ≡ 1 [MOD ordCompl[2] (ordC ψ)] ∧ (pOne ψ).Coprime (2 * ψ.N * pK ψ)) ∧ Module.finrank ℚ (Kstar (pK ψ)) = 2 := by
  intro ψ
  have hN : ψ.N ≠ 0 := NeZero.ne _
  have hne1 : {p | Nat.Prime p ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime ψ.N}.Nonempty := by
    obtain ⟨p, hpgt, hp, hpm⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 3) (by decide) (ψ.N + 7)
    refine ⟨p, hp, ?_, by omega, ?_⟩
    · have h3 : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by simpa using hpm
      rw [ZMod.natCast_eq_natCast_iff'] at h3
      simpa using h3
    · rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
      omega
  have h1 : (pK ψ).Prime ∧ pK ψ % 4 = 3 ∧ 7 ≤ pK ψ ∧ (pK ψ).Coprime ψ.N := Nat.sInf_mem hne1
  have hord : ordC ψ ≠ 0 := (orderOf_pos _).ne'
  have hk : ordC ψ / 2 ^ (ordC ψ).factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hord).ne'
  have hm : 0 < 2 * ψ.N * pK ψ := by
    have := h1.1.pos
    have := Nat.pos_of_ne_zero hN
    positivity
  have hne2 : {p | Nat.Prime p ∧ p ≡ 1 [MOD ordC ψ / 2 ^ (ordC ψ).factorization 2] ∧
      p.Coprime (2 * ψ.N * pK ψ)}.Nonempty := by
    obtain ⟨p, hp, hpgt, hpm⟩ := Nat.exists_prime_gt_modEq_one (2 * ψ.N * pK ψ) hk
    refine ⟨p, hp, hpm, ?_⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd hm h
    omega
  have h2 := Nat.sInf_mem hne2
  exact ⟨h1, h2, finrank_kstar _ h1.1.pos⟩
end

