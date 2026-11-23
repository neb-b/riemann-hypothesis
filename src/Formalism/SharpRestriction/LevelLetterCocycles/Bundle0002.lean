module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GenOfKiller
section
namespace Formalism.MainNotions.UnusedSlot80.UGen

theorem span_le_card {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {g : ℕ} (v : Fin g → M) (N : Submodule R M)
    (hN : N ≤ Submodule.span R (Set.range v)) :
    ∃ (g₀ : ℕ) (w : Fin g₀ → M), g₀ ≤ g ∧ (∀ i, w i ∈ N) ∧
      N = Submodule.span R (Set.range w) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    (N.comap (Finsupp.linearCombination R v))
  refine ⟨n, fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R), ?_, ?_, ?_⟩
  · have h1 := Module.finrank_eq_card_basis b
    have h2 := Submodule.finrank_le (N.comap (Finsupp.linearCombination R v))
    have h3 := Module.finrank_eq_card_basis
      (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    simp only [Fintype.card_fin] at h1 h3
    omega
  · intro i
    exact (b i).2
  · have hb : Submodule.span R (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
        N.comap (Finsupp.linearCombination R v) := by
      have e : (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
          (N.comap (Finsupp.linearCombination R v)).subtype '' Set.range b := by
        ext x; simp
      rw [e, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    have e2 : (Set.range fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R)) =
        (Finsupp.linearCombination R v) '' Set.range fun i => ((b i : _) : Fin g →₀ R) := by
      ext x; simp
    rw [e2, ← Submodule.map_span, hb, Submodule.map_comap_eq,
      Finsupp.range_linearCombination, inf_eq_right.mpr hN]

private theorem mkQ_mem_span_of_mem_sup_lemma {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P : Submodule R V) (u : ι → V) {x : V} (hx : x ∈ Submodule.span R (Set.range u) ⊔ P) :
    P.mkQ x ∈ Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
  obtain ⟨a, ha, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
  have hp0 : P.mkQ p = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hp
  rw [map_add (f := _), hp0, add_zero]
  have hle : (Submodule.span R (Set.range u)).map P.mkQ ≤
      Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hle (Submodule.mem_map_of_mem ha)

theorem gen_of_killer {R V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] (Msub Psub Isub : Submodule R V) (hIM : Isub ≤ Msub)
    {ι : Type*} [Finite ι] (F : ι → V) (hfg : Msub ≤ Submodule.span R (Set.range F) ⊔ Psub)
    (lR t : R) {g : ℕ} (v : Fin g → V)
    (hK : ∀ f ∈ Isub, ∃ K : ℕ, (lR ^ K * t) • f ∈ Submodule.span R (Set.range v) ⊔ Psub)
    (hsat : ∀ K : ℕ, ∀ f ∈ Msub, (lR ^ K * t) • f ∈ Psub → f ∈ Psub) :
    ∃ (g₀ : ℕ) (J : Fin g₀ → V), g₀ ≤ g ∧ (∀ i, J i ∈ Isub) ∧
      ∀ f ∈ Isub, ∃ o : Fin g₀ → R, f - ∑ i, o i • J i ∈ Psub := by
  classical
  let W : Submodule R (V ⧸ Psub) := Submodule.span R (Set.range fun i => Psub.mkQ (v i))
  let B : ℕ → Submodule R (V ⧸ Psub) := fun K =>
    W.comap ((lR ^ K * t) • (LinearMap.id : (V ⧸ Psub) →ₗ[R] V ⧸ Psub))
  have hBmono : Monotone B := by
    intro K K' hKK' q hq
    change (lR ^ K * t) • q ∈ W at hq
    change (lR ^ K' * t) • q ∈ W
    have e : lR ^ K' * t = lR ^ (K' - K) * (lR ^ K * t) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hKK']
    rw [e, mul_smul]
    exact W.smul_mem _ hq
  have hmemB : ∀ f ∈ Isub, ∃ K, Psub.mkQ f ∈ B K := by
    intro f hf
    obtain ⟨K, hKf⟩ := hK f hf
    refine ⟨K, ?_⟩
    change (lR ^ K * t) • Psub.mkQ f ∈ W
    rw [← map_smul]
    exact mkQ_mem_span_of_mem_sup_lemma Psub v hKf
  have hIle : Isub.map Psub.mkQ ≤ Submodule.span R (Set.range fun i => Psub.mkQ (F i)) := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hq
    exact mkQ_mem_span_of_mem_sup_lemma Psub F (hfg (hIM hf))
  haveI hT : IsNoetherian R (Submodule.span R (Set.range fun i => Psub.mkQ (F i))) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  haveI hIN : IsNoetherian R (Isub.map Psub.mkQ) := isNoetherian_of_le hIle
  have hfgI : (Isub.map Psub.mkQ).FG :=
    (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
  obtain ⟨S, hS⟩ := hfgI
  have hSB : ∀ x ∈ S, ∃ K, x ∈ B K := by
    intro x hx
    have hxI : x ∈ Isub.map Psub.mkQ := by
      rw [← hS]; exact Submodule.subset_span (Finset.mem_coe.mpr hx)
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hxI
    exact hmemB f hf
  choose! Kf hKf using hSB
  obtain ⟨K, hIB⟩ : ∃ K, Isub.map Psub.mkQ ≤ B K := by
    refine ⟨S.sup Kf, ?_⟩
    rw [← hS, Submodule.span_le]
    intro x hx
    exact hBmono (Finset.le_sup (Finset.mem_coe.mp hx)) (hKf x (Finset.mem_coe.mp hx))
  have hN : Isub.map ((lR ^ K * t) • Psub.mkQ) ≤
      Submodule.span R (Set.range fun i => Psub.mkQ (v i)) := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    have h1 := hIB (Submodule.mem_map_of_mem hf)
    change (lR ^ K * t) • Psub.mkQ f ∈ W at h1
    rw [LinearMap.smul_apply]
    exact h1
  obtain ⟨g₀, w, hg₀, hwN, hNw⟩ := span_le_card (fun i => Psub.mkQ (v i)) _ hN
  have hJ : ∀ i, ∃ f ∈ Isub, ((lR ^ K * t) • Psub.mkQ) f = w i :=
    fun i => Submodule.mem_map.mp (hwN i)
  choose J hJI hJw using hJ
  refine ⟨g₀, J, hg₀, hJI, ?_⟩
  intro f hf
  have hφf : ((lR ^ K * t) • Psub.mkQ) f ∈ Submodule.span R (Set.range w) := by
    rw [← hNw]; exact Submodule.mem_map_of_mem hf
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R)).mp hφf
  refine ⟨o, hsat K _ ?_ ?_⟩
  · apply hIM
    exact Isub.sub_mem hf (Isub.sum_mem fun i _ => Isub.smul_mem _ (hJI i))
  · have h0 : ((lR ^ K * t) • Psub.mkQ) (f - ∑ i, o i • J i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul, hJw]
      rw [ho, sub_self]
    rw [LinearMap.smul_apply, ← map_smul] at h0
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h0

end Formalism.MainNotions.UnusedSlot80.UGen
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd
section
namespace Formalism.MainNotions.UnusedSlot80.LTE

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℚ))

theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (le_of_eq v.map_one.symm)) (v.map_add _ _)

theorem intCast_nonneg (m : ℤ) : 0 ≤ v (m : K) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [Int.cast_natCast]; exact natCast_nonneg v n
  · rw [Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]; exact natCast_nonneg v n

private theorem withTop_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)

theorem natCast_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) (hv : v (p : K) = 1) {m : ℕ}
    (hm : ¬ p ∣ m) : v (m : K) = 0 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h1 : ((Nat.gcd p m : ℕ) : ℤ) = (p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m :=
    Nat.gcd_eq_gcd_ab p m
  rw [hcop.gcd_eq_one] at h1
  have hK : (1 : K) = (p : K) * (Nat.gcdA p m : K) + (m : K) * (Nat.gcdB p m : K) := by
    have h2 := congrArg (fun z : ℤ => (z : K)) h1
    push_cast at h2
    exact h2
  have h0 := natCast_nonneg v m
  by_contra hne
  have hpos : 0 < v (m : K) := lt_of_le_of_ne h0 (Ne.symm hne)
  have h3 : 0 < v ((p : K) * (Nat.gcdA p m : K)) := by
    rw [AddValuation.map_mul, hv]
    exact lt_of_lt_of_le withTop_zero_lt_one (le_add_of_nonneg_right (intCast_nonneg v _))
  have h4 : 0 < v ((m : K) * (Nat.gcdB p m : K)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (intCast_nonneg v _))
  have h5 := v.map_add ((p : K) * (Nat.gcdA p m : K)) ((m : K) * (Nat.gcdB p m : K))
  rw [← hK, AddValuation.map_one] at h5
  exact absurd h5 (not_le.2 (lt_min h3 h4))

theorem pow_nonneg' {x : K} (hx : 0 ≤ v x) (k : ℕ) : 0 ≤ v (x ^ k) := by
  rw [AddValuation.map_pow]
  exact nsmul_nonneg hx k

private theorem v_finset_sum_nonneg_of_forall {ι : Type*} (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun y => 0 ≤ v y)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b))
    (by rw [AddValuation.map_zero]; exact le_top) h

theorem geom_nonneg {x : K} (hx : 0 ≤ v x) (k : ℕ) : 0 ≤ v (∑ j ∈ Finset.range k, x ^ j) :=
  v_finset_sum_nonneg_of_forall v _ _ (fun j _ => pow_nonneg' v hx j)

private theorem v_add_eq_left_of_v_lt {a b : K} (h : v a < v b) : v (a + b) = v a := by
  apply le_antisymm
  · have h1 := v.map_add (a + b) (-b)
    rw [AddValuation.map_neg, add_neg_cancel_right] at h1
    rcases min_le_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)
  · exact le_trans (le_min le_rfl h.le) (v.map_add a b)

theorem v_x_zero {x : K} (hy : 0 < v (x - 1)) : v x = 0 := by
  have h1 := v_add_eq_left_of_v_lt v (a := 1) (b := x - 1) (by rw [AddValuation.map_one]; exact hy)
  rwa [show (1 : K) + (x - 1) = x by ring, AddValuation.map_one] at h1

theorem geom_expand (x : K) (k : ℕ) :
    ∑ j ∈ Finset.range k, x ^ j =
      (k : K) + (x - 1) * ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, x ^ i := by
  rw [Finset.mul_sum]
  have h1 : ∀ j ∈ Finset.range k, (x - 1) * ∑ i ∈ Finset.range j, x ^ i = x ^ j - 1 :=
    fun j _ => by rw [mul_comm, geom_sum_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

theorem val_pow_sub_one_coprime {p : ℕ} (hp : p.Prime) (hv : v (p : K) = 1) {x : K}
    (hy : 0 < v (x - 1)) {m : ℕ} (hm : ¬ p ∣ m) : v (x ^ m - 1) = v (x - 1) := by
  have hx : 0 ≤ v x := (v_x_zero v hy).ge
  have hm0 : v (m : K) = 0 := natCast_eq_zero_of_not_dvd v hp hv hm
  have hlt : v (m : K) <
      v ((x - 1) * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, x ^ i) := by
    rw [hm0, AddValuation.map_mul]
    exact lt_of_lt_of_le hy (le_add_of_nonneg_right
      (v_finset_sum_nonneg_of_forall v _ _ (fun j _ => geom_nonneg v hx j)))
  have hS : v (∑ j ∈ Finset.range m, x ^ j) = 0 := by
    rw [geom_expand, v_add_eq_left_of_v_lt v hlt, hm0]
  rw [← geom_sum_mul x m, AddValuation.map_mul, hS, zero_add]

private theorem withTop_one_lt_one_add_one : (1 : WithTop ℚ) < 1 + 1 := by
  exact_mod_cast (by norm_num : (1 : ℚ) < 1 + 1)

private theorem one_le_v_natCast_of_dvd {p : ℕ} (hv : v (p : K) = 1) {n : ℕ} (h : p ∣ n) :
    1 ≤ v (n : K) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, AddValuation.map_mul, hv]
  exact le_add_of_nonneg_right (natCast_nonneg v c)

theorem val_pow_p_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) : v (x ^ p - 1) = v (x - 1) + 1 := by
  have hx : 0 ≤ v x := (v_x_zero v (lt_of_lt_of_le withTop_zero_lt_one hy)).ge
  have hid : ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, x ^ i =
      (∑ j ∈ Finset.range p, (j : K)) + (x - 1) *
        ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => geom_expand x j)
  have hN : 1 ≤ v (∑ j ∈ Finset.range p, (j : K)) := by
    rw [show (∑ j ∈ Finset.range p, (j : K)) = ((∑ j ∈ Finset.range p, j : ℕ) : K) by
      rw [Nat.cast_sum]]
    apply one_le_v_natCast_of_dvd v hv
    have hd : p ∣ (∑ i ∈ Finset.range p, i) * 2 := by
      rw [Finset.sum_range_id_mul_two]
      exact dvd_mul_right p (p - 1)
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
  have hT : 0 ≤ v (∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l) :=
    v_finset_sum_nonneg_of_forall v _ _
      (fun j _ => v_finset_sum_nonneg_of_forall v _ _ (fun i _ => geom_nonneg v hx i))
  have hinner : 1 ≤ v ((∑ j ∈ Finset.range p, (j : K)) + (x - 1) *
      ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l) := by
    refine le_trans (le_min hN ?_) (v.map_add _ _)
    rw [AddValuation.map_mul]
    exact le_trans hy (le_add_of_nonneg_right hT)
  have hlt : v (p : K) < v ((x - 1) * ((∑ j ∈ Finset.range p, (j : K)) + (x - 1) *
      ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l)) := by
    rw [hv, AddValuation.map_mul]
    exact lt_of_lt_of_le withTop_one_lt_one_add_one (add_le_add hy hinner)
  have hsum : v (∑ j ∈ Finset.range p, x ^ j) = 1 := by
    rw [geom_expand, hid, v_add_eq_left_of_v_lt v hlt, hv]
  rw [← geom_sum_mul x p, AddValuation.map_mul, hsum, add_comm]

private theorem withTop_rat_natCast_nonneg (k : ℕ) : (0 : WithTop ℚ) ≤ (k : WithTop ℚ) := by
  exact_mod_cast (Nat.cast_nonneg k : (0 : ℚ) ≤ k)

theorem val_pow_pk_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) (k : ℕ) : v (x ^ (p ^ k) - 1) = v (x - 1) + (k : WithTop ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 1 ≤ v (x ^ (p ^ k) - 1) := by
      rw [ih]
      exact le_trans hy (le_add_of_nonneg_right (withTop_rat_natCast_nonneg k))
    rw [pow_succ p k, pow_mul x (p ^ k) p, val_pow_p_sub_one v hp hp2 hv hk, ih,
      Nat.cast_succ, add_assoc]

theorem val_pow_sub_one_nat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) {m : ℕ} (hm : m ≠ 0) :
    v (x ^ m - 1) = v (x - 1) + (padicValNat p m : WithTop ℚ) := by
  haveI := Fact.mk hp
  obtain ⟨n, hn⟩ := ((_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) : p ^ padicValNat p m ∣ m)
  have hpn : ¬ p ∣ n := by
    rintro ⟨c, rfl⟩
    exact pow_succ_padicValNat_not_dvd hm ⟨c, hn.trans (by rw [← Nat.padicValNat_def]; ring)⟩
  have key : x ^ m = (x ^ (p ^ padicValNat p m)) ^ n := by
    rw [← pow_mul, ← hn]
  have hz := val_pow_pk_sub_one v hp hp2 hv hy (padicValNat p m)
  have hzpos : 0 < v (x ^ (p ^ padicValNat p m) - 1) := by
    rw [hz]
    exact lt_of_lt_of_le withTop_zero_lt_one
      (le_trans hy (le_add_of_nonneg_right (withTop_rat_natCast_nonneg _)))
  rw [key, val_pow_sub_one_coprime v hp hv hzpos hpn, hz]

theorem val_zpow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) {m : ℤ} (hm : m ≠ 0) :
    v (x ^ m - 1) = v (x - 1) + (padicValInt p m : WithTop ℚ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hm rfl
    have hpv : padicValInt p (n : ℤ) = padicValNat p n := by simp [padicValInt, ← Nat.padicValNat_def]
    rw [zpow_natCast, hpv]
    exact val_pow_sub_one_nat v hp hp2 hv hy hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hm (by simp)
    have hpv : padicValInt p (-(n : ℤ)) = padicValNat p n := by simp [padicValInt, ← Nat.padicValNat_def]
    have hvx : v x = 0 := v_x_zero v (lt_of_lt_of_le withTop_zero_lt_one hy)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [AddValuation.map_zero] at hvx
      simp at hvx
    have hxn : x ^ n ≠ 0 := pow_ne_zero n hx0
    have hvxn : v (x ^ n) = 0 := by
      rw [AddValuation.map_pow, hvx, smul_zero]
    have hinv : v ((x ^ n)⁻¹) = 0 := by
      have h1 : v ((x ^ n)⁻¹) + v (x ^ n) = 0 := by
        rw [← AddValuation.map_mul, inv_mul_cancel₀ hxn, AddValuation.map_one]
      rwa [hvxn, add_zero] at h1
    have hrw : x ^ (-(n : ℤ)) - 1 = -((x ^ n)⁻¹ * (x ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hxn, mul_one]
      ring
    rw [hrw, AddValuation.map_neg, AddValuation.map_mul, hinv, zero_add, hpv]
    exact val_pow_sub_one_nat v hp hp2 hv hy hn

end Formalism.MainNotions.UnusedSlot80.LTE
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.NormLtOneIffToZMod
section
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.Cyc

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_lt_one_iff_toZMod (x : ℤ_[l]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by

  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_le_inv_of_lt_one (x : ℤ_[l]) (h : ‖x‖ < 1) : ‖x‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by

  rw [show (-((1 : ℕ) : ℤ)) = -1 by simp, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
  simpa using h

theorem teich (c : ℤ_[l]) (hc : ‖c‖ = 1) : ∃ ω : ℤ_[l], ω ^ (l - 1) = 1 ∧ ‖ω - c‖ < 1 := by

  classical
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hFdef
  have hc0 : PadicInt.toZMod c ≠ 0 := fun h0 => by
    have := (norm_lt_one_iff_toZMod c).mpr h0
    rw [hc] at this
    exact lt_irrefl _ this
  have hn : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    rw [norm_lt_one_iff_toZMod, map_natCast, ZMod.natCast_eq_zero_iff] at h
    have h2 := hl.out.two_le
    have := Nat.le_of_dvd (by omega) h
    omega
  have e1 : Polynomial.aeval c F = c ^ (l - 1) - 1 := by simp [hFdef]
  have e2 : Polynomial.aeval c (Polynomial.derivative F) = ((l - 1 : ℕ) : ℤ_[l]) * c ^ (l - 1 - 1) := by
    simp [hFdef, Polynomial.derivative_X_pow]
  have hF' : ‖Polynomial.aeval c (Polynomial.derivative F)‖ = 1 := by
    rw [e2, norm_mul, norm_pow, hc, one_pow, mul_one, hn]
  have hF : ‖Polynomial.aeval c F‖ < 1 := by
    rw [e1, norm_lt_one_iff_toZMod, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hc0, sub_self]
  obtain ⟨z, hz, hzc, -⟩ := hensels_lemma (F := F) (a := c) (by rw [hF', one_pow]; exact hF)
  refine ⟨z, ?_, ?_⟩
  · simpa [hFdef, sub_eq_zero] using hz
  · rw [hF'] at hzc; exact hzc

theorem pow_approx (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : ‖u - 1‖ = (l : ℝ)⁻¹) (c : ℤ_[l]) (hc : ‖c - 1‖ < 1)
    (n : ℕ) : ∃ k : ℕ, ‖u ^ k - c‖ ≤ (l : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  have hp := hl.out
  have h3 : 3 ≤ l := by have := hp.two_le; omega

  have hu1 : u - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, hu]; simp
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hu1
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hrn : ‖r‖ = 1 := by
    have : ‖u - 1‖ = ‖r‖ * (l : ℝ)⁻¹ := by rw [← hr, pow_one, norm_mul, PadicInt.norm_p]
    rw [hu] at this
    have hne : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hlpos.ne'
    field_simp at this
    linarith

  set a : ℤ := ((PadicInt.toZModPow (n + 1) r).val : ℤ) with ha_def
  have ha_cast : (a : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) r := by
    rw [ha_def, Int.cast_natCast, ZMod.natCast_zmod_val]
  have ha : ¬ (l : ℤ) ∣ a := by
    intro hdvd
    have h1 : (a : ZMod (l ^ 1)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hdvd
    have h2 : (a : ZMod (l ^ 1)) = PadicInt.toZModPow 1 r := by
      rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply, ← ha_cast, map_intCast]
    rw [h2, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow, hrn] at h1
    have : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
      rw [Nat.cast_one, zpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    linarith
  have hord : orderOf (1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a) = l ^ n :=
    ZMod.orderOf_one_add_mul_prime_pow hp 1 (by omega) a ha n
  have hub : PadicInt.toZModPow (n + 1) u = 1 + (l : ZMod (l ^ (n + 1))) ^ 1 * a := by
    have : u = 1 + (l : ℤ_[l]) ^ 1 * r := by rw [pow_one, mul_comm]; rw [pow_one] at hr; rw [hr]; ring
    rw [this, map_add (f := _), map_one, map_mul, map_pow, map_natCast, ha_cast]

  have huu : IsUnit (PadicInt.toZModPow (n + 1) u) := by
    apply IsUnit.map
    rw [PadicInt.isUnit_iff]
    have : u = 1 + (u - 1) := by ring
    rw [this]
    have h1 : ‖(u - 1)‖ < ‖(1 : ℤ_[l])‖ := by
      rw [hu, norm_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    rw [← norm_one (α := ℤ_[l])]
    exact PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)
  have hcu : IsUnit (PadicInt.toZModPow (n + 1) c) := by
    apply IsUnit.map
    rw [PadicInt.isUnit_iff]
    have : c = 1 + (c - 1) := by ring
    rw [this]
    have h1 : ‖(c - 1)‖ < ‖(1 : ℤ_[l])‖ := by rw [norm_one]; exact hc
    rw [← norm_one (α := ℤ_[l])]
    exact PadicInt.norm_add_eq_max_of_ne (ne_of_lt h1).symm |>.trans (max_eq_left h1.le)
  set U := huu.unit
  set C := hcu.unit
  have hdiv : l ^ 1 ∣ l ^ (n + 1) := pow_dvd_pow l (by omega)
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hker : ∀ x : ℤ_[l], ‖x - 1‖ < 1 → ∀ hx : IsUnit (PadicInt.toZModPow (n + 1) x), hx.unit ∈ (ZMod.unitsMap hdiv).ker := by
    intro x hx hxu
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, IsUnit.unit_spec]
    change ZMod.castHom hdiv (ZMod (l ^ 1)) (PadicInt.toZModPow (n + 1) x) = 1
    rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega),
      ← sub_eq_zero, ← map_one (PadicInt.toZModPow 1), ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    exact norm_le_inv_of_lt_one _ hx
  have hUk : U ∈ (ZMod.unitsMap hdiv).ker := hker u (by rw [hu]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) huu
  have hCk : C ∈ (ZMod.unitsMap hdiv).ker := hker c hc hcu

  have hcardG : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]
  have hrange : (ZMod.unitsMap hdiv).range = ⊤ := MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hdiv)
  have hcardK : Nat.card (ZMod.unitsMap hdiv).ker = l ^ n := by
    have h1 := Subgroup.card_mul_index (ZMod.unitsMap hdiv).ker
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcardH, hcardG] at h1
    have hl1 : 0 < l - 1 := by omega
    exact Nat.eq_of_mul_eq_mul_right hl1 h1
  have hzp : Subgroup.zpowers U = (ZMod.unitsMap hdiv).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hUk
    · rw [hcardK, Nat.card_zpowers, ← orderOf_units, IsUnit.unit_spec, hub, hord]
  rw [← hzp, ← mem_powers_iff_mem_zpowers] at hCk
  obtain ⟨k, hk⟩ := hCk
  refine ⟨k, ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_pow,
    sub_eq_zero]
  have := congrArg Units.val hk
  simpa [U, C] using this

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.Cyc
end
end

