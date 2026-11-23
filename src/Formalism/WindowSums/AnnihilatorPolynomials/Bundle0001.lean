module

public import Formalism.WindowSums.Statement

@[expose] public section

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.DistinctTerms
section
noncomputable section

namespace Formalism.WindowSums

open PowerSeries

theorem mem_span_iff_of_distinct_exponents : DistinctTerms := by
  intro O _ _ ϖ hϖ hnu ι I w e m B s hw he
  classical
  constructor
  · intro hmem
    by_contra hbad
    push_neg at hbad
    obtain ⟨i₁, hi₁, hb₁, hs₁⟩ := hbad
    have hJne : (I.filter fun i => e i < B ∧ m i < s).Nonempty :=
      ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hb₁, hs₁⟩⟩
    obtain ⟨i₀, hi₀J, hmin⟩ := (I.filter fun i => e i < B ∧ m i < s).exists_min_image e hJne
    obtain ⟨hi₀, hB, hs⟩ := Finset.mem_filter.mp hi₀J
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have hcoef := congrArg (PowerSeries.coeff (e i₀)) hab
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), mul_comm a, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_mul_C, map_sum] at hcoef
    have hterm : ∀ i ∈ I, PowerSeries.coeff (e i₀) (w i * X ^ e i * C (ϖ ^ m i)) =
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      intro i _
      rw [PowerSeries.coeff_mul_C, mul_comm (w i), PowerSeries.coeff_X_pow_mul']
    rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hi₀, if_pos le_rfl,
      Nat.sub_self] at hcoef
    have hrest : ϖ ^ s ∣ ∑ i ∈ I.erase i₀,
        (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
      refine Finset.dvd_sum fun i hi => ?_
      obtain ⟨hne, hiI⟩ := Finset.mem_erase.mp hi
      by_cases hle : e i ≤ e i₀
      · rw [if_pos hle]
        have hlt : e i < e i₀ := lt_of_le_of_ne hle fun h => hne (he hiI hi₀ h)
        have hms : s ≤ m i := by
          by_contra hms
          push_neg at hms
          have := hmin i (Finset.mem_filter.mpr ⟨hiI, by omega, hms⟩)
          omega
        exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hms) _
      · rw [if_neg hle, zero_mul]
        exact dvd_zero _
    have hdvd : ϖ ^ s ∣ PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ := by
      have h2 : PowerSeries.coeff 0 (w i₀) * ϖ ^ m i₀ =
          PowerSeries.coeff (e i₀) b * ϖ ^ s - ∑ i ∈ I.erase i₀,
            (if e i ≤ e i₀ then PowerSeries.coeff (e i₀ - e i) (w i) else 0) * ϖ ^ m i := by
        rw [hcoef]; ring
      rw [h2]
      exact dvd_sub (dvd_mul_left _ _) hrest
    have hu : IsUnit (PowerSeries.coeff 0 (w i₀)) := by
      have := (hw i₀ hi₀).map (PowerSeries.constantCoeff (R := O))
      simpa using this
    have hsplit : ϖ ^ s = ϖ ^ m i₀ * ϖ ^ (s - m i₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hs.le]
    rw [hsplit, mul_comm (PowerSeries.coeff 0 (w i₀))] at hdvd
    have hd2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ)).mp hdvd
    have hd3 : ϖ ∣ PowerSeries.coeff 0 (w i₀) :=
      (dvd_pow_self ϖ (by omega)).trans hd2
    exact hnu (isUnit_of_dvd_unit hd3 hu)
  · intro h
    refine Ideal.sum_mem _ fun i hi => ?_
    rcases h i hi with hb | hs
    · have hx : (X : PowerSeries O) ^ B ∈
          Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = X ^ B * (w i * X ^ (e i - B) * C (ϖ ^ m i)) := by
        rw [show e i = B + (e i - B) by omega, pow_add]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hx
    · have hc : C (ϖ ^ s) ∈ Ideal.span {(X : PowerSeries O) ^ B, C (ϖ ^ s)} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have heq : w i * X ^ e i * C (ϖ ^ m i) = C (ϖ ^ s) * (w i * X ^ e i * C (ϖ ^ (m i - s))) := by
        rw [show m i = s + (m i - s) by omega, pow_add, map_mul]
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [heq]
      exact Ideal.mul_mem_right _ _ hc

end Formalism.WindowSums
end
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.EvalOneSmulDecomposition
section
namespace Formalism.WindowSums

open Polynomial

theorem annihilatorPoly_kills : KillerKills := by
  intro ℓ _ c ell JJ V _ _ T
  refine ⟨?_, ?_⟩
  · rintro x ⟨i, hi, hx⟩
    have hsplit : PP ℓ c ell JJ = ((∏ k ∈ (JJ.erase 0).erase i, (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (k * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k) * (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
      unfold PP
      rw [← Finset.mul_prod_erase _ _ hi]
      ring
    have hk : Polynomial.aeval T (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) x = 0 := by
      simp [hx]
    rw [hsplit, map_mul, Module.End.mul_apply, hk, map_zero]
  · intro v hv
    have hS : Polynomial.aeval T (∑ k ∈ Finset.range (ℓ ^ ell), (Polynomial.X : Polynomial ℤ_[ℓ]) ^ k)
        (T v - v) = 0 := by
      have h1 : T v - v = Polynomial.aeval T (Polynomial.X - 1 : Polynomial ℤ_[ℓ]) v := by simp
      rw [h1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul]
      simp [hv]
    unfold PP
    rw [map_mul, Module.End.mul_apply, hS, map_zero]

end Formalism.WindowSums
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.Lagrange
section
noncomputable section

namespace Formalism.WindowSums

open Polynomial

private lemma aeval_prod_X_sub_C_eq_zero_of_subset {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    (T : Module.End R V) {ι : Type} [DecidableEq ι] (A B : Finset ι) (γ : ι → R) (x : V)
    (hAB : A ⊆ B) (hA : aeval T (∏ k ∈ A, (X - C (γ k))) x = 0) :
    aeval T (∏ k ∈ B, (X - C (γ k))) x = 0 := by
  rw [← Finset.prod_sdiff hAB, map_mul, Module.End.mul_apply, hA, map_zero]

theorem lagrange_annihilation : Lagrange := by
  intro R _ _ V _ _ T ι _ I S γ d x hSI hinj hS hIS hdiv
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI
    have hS0 : S = ∅ := Finset.subset_empty.mp hSI
    subst hS0
    simp at hS
    simp [hS]
  choose! c hc using hdiv

  have key : ∑ k ∈ I, C (c k) * ∏ m ∈ I.erase k, (X - C (γ m)) = C d := by
    rw [← sub_eq_zero]
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (I.image γ)
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_sub, eval_finsetSum, eval_C, sub_eq_zero]
      rw [Finset.sum_eq_single j]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        rw [hc j hj, mul_comm]
      · intro k hk hkj
        rw [eval_mul, eval_prod]
        apply mul_eq_zero_of_right
        apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨fun h => hkj h.symm, hj⟩)
        simp
      · intro hj'; exact absurd hj hj'
    · rw [Finset.card_image_of_injOn hinj]
      have hpos : 0 < I.card := Finset.card_pos.mpr hI
      have hdeg : ∀ k ∈ I, (C (c k) * ∏ m ∈ I.erase k, (X - C (γ m))).natDegree ≤ I.card - 1 := by
        intro k hk
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_prod_le _ _).trans ?_
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        rw [Finset.card_erase_of_mem hk]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C, max_lt_iff]
      refine ⟨lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ hdeg) (by omega), hpos⟩
  have h := congrArg (fun p => aeval T p x) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, aeval_C] at h
  rw [LinearMap.sum_apply] at h
  rw [Module.algebraMap_end_apply] at h
  rw [← h]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]
  by_cases hkS : k ∈ S
  · have : I \ S ⊆ I.erase k := by
      intro m hm
      rw [Finset.mem_sdiff] at hm
      exact Finset.mem_erase.mpr ⟨fun h => hm.2 (h ▸ hkS), hm.1⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hIS, smul_zero]
  · have : S ⊆ I.erase k := by
      intro m hm
      exact Finset.mem_erase.mpr ⟨fun h => hkS (h ▸ hm), hSI hm⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hS, smul_zero]

end Formalism.WindowSums
end
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.ValProd
section
namespace Formalism.WindowSums

open Finset

section ValProdAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma vp_val_neg (x : ℤ_[ℓ]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 : (-1 : ℤ_[ℓ]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hm1 : (-1 : ℤ_[ℓ]).valuation = 0 := by
    have h := PadicInt.valuation_mul h1 h1
    rw [neg_one_mul, neg_neg, PadicInt.valuation_one] at h
    omega
  rw [← neg_one_mul x, PadicInt.valuation_mul h1 hx, hm1, zero_add]

lemma vp_val_prod {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ_[ℓ])
    (h : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i) ≠ 0 ∧ (∏ i ∈ S, f i).valuation = ∑ i ∈ S, (f i).valuation := by
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [PadicInt.valuation_one]
  · intro a S ha ih h
    have hS : ∀ i ∈ S, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha0 : f a ≠ 0 := h a (Finset.mem_insert_self a S)
    obtain ⟨h1, h2⟩ := ih hS
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 h1, by rw [PadicInt.valuation_mul ha0 h1, h2]⟩

private theorem prime_pow_ne_zero_and_valuation_eq (n : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ n ≠ 0 ∧ ((ℓ : ℤ_[ℓ]) ^ n).valuation = n := by
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by
    intro h
    have h' := PadicInt.valuation_p (p := ℓ)
    rw [h, PadicInt.valuation_zero] at h'
    exact absurd h' (by norm_num)
  induction n with
  | zero => simp [PadicInt.valuation_one]
  | succ n ih =>
    refine ⟨pow_ne_zero _ hℓ0, ?_⟩
    rw [pow_succ, PadicInt.valuation_mul ih.1 hℓ0, ih.2, PadicInt.valuation_p]

lemma vp_sum_padicValNat (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, padicValNat ℓ i = padicValNat ℓ M.factorial := by
  induction M with
  | zero => simp [Nat.padicValNat_def]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega : n + 1 ≠ 0) (Nat.factorial_ne_zero n)]
    omega

end ValProdAux

theorem valProd_of (hZ : ZpowVal) : ValProd := by
  unfold ValProd
  unfold ZpowVal at hZ
  intro ℓ hp u s hs h2 hv
  have key : ∀ j : ℤ, j ≠ 0 →
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
    intro j hj
    obtain ⟨h1, h2'⟩ := hZ ℓ u s hs h2 hv j hj
    rw [← neg_sub, vp_val_neg, h2']
    exact ⟨neg_ne_zero.mpr h1, rfl⟩
  refine ⟨fun M => ?_, fun J hJ => ?_⟩
  · have hf : ∀ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) ≠ 0 ∧
        (1 - (u : ℤ_[ℓ]) ^ i).valuation = s + padicValNat ℓ i := by
      intro i hi
      have hi0 : (i : ℤ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hk := key i hi0
      have e : ((u ^ (i : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ i := by
        rw [zpow_natCast, Units.val_pow_eq_pow_val]
      have hv' : padicValInt ℓ (i : ℤ) = padicValNat ℓ i := by
        rw [padicValInt.of_nat, Nat.padicValNat_def]
      rw [e, hv'] at hk
      exact hk
    obtain ⟨h1, h2'⟩ := vp_val_prod (Finset.Icc 1 M)
      (fun i => 1 - (u : ℤ_[ℓ]) ^ i) (fun i hi => (hf i hi).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun i hi => (hf i hi).2), Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, smul_eq_mul,
      vp_sum_padicValNat, Nat.add_sub_cancel]
  · have hf : ∀ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
        (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
      intro j hj
      have hj0 : -j ≠ 0 := neg_ne_zero.mpr (fun h => hJ (by rw [← h]; exact hj))
      obtain ⟨h1, h2'⟩ := key (-j) hj0
      refine ⟨h1, h2'.trans ?_⟩
      simp [padicValInt]
    obtain ⟨h1, h2'⟩ := vp_val_prod J
      (fun j => 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun j hj => (hf j hj).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun j hj => (hf j hj).2), Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul]

theorem killerVal_of (hZ : ZpowVal) : KillerVal := by
  unfold KillerVal
  unfold ZpowVal at hZ
  intro ℓ hp h2 c hc e JJ
  have h22 : ℓ = 2 → 2 ≤ 1 := fun h => absurd h h2
  have hf : ∀ i ∈ JJ.erase 0,
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = 1 + e + padicValInt ℓ i := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hp0 : ((ℓ : ℤ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hj : i * (ℓ : ℤ) ^ e ≠ 0 := mul_ne_zero hi0 hp0
    obtain ⟨h1, h2'⟩ := hZ ℓ c 1 le_rfl h22 hc _ hj
    rw [← neg_sub, vp_val_neg, h2', padicValInt.mul hi0 hp0]
    refine ⟨neg_ne_zero.mpr h1, ?_⟩
    have hpe : padicValInt ℓ ((ℓ : ℤ) ^ e) = e := by
      simp [padicValInt, Int.natAbs_pow]
    omega
  obtain ⟨h1, h2'⟩ := vp_val_prod (JJ.erase 0)
    (fun i => 1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun i hi => (hf i hi).1)
  obtain ⟨hP1, hP2⟩ := prime_pow_ne_zero_and_valuation_eq (ℓ := ℓ) e
  have hev : (PP ℓ c e JJ).eval 1 =
      (∏ i ∈ JJ.erase 0, (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) * (ℓ : ℤ_[ℓ]) ^ e := by
    simp [PP, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  rw [hev]
  refine ⟨mul_ne_zero h1 hP1, ?_⟩
  rw [PadicInt.valuation_mul h1 hP1, hP2, h2', Finset.sum_congr rfl (fun i hi => (hf i hi).2)]

end Formalism.WindowSums
end

-- bundled from Formalism.WindowSums.AnnihilatorPolynomials.WindowSum
section
noncomputable section

namespace Formalism.WindowSums

open Finset

lemma windowSum_count (a : ℤ) (L : ℕ) (r : ℤ) (hr : 0 < r) :
    ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤ (L : ℝ) / (r : ℝ) + 1 := by
  have hmaps : ∀ x ∈ (Finset.Ico a (a + L)).filter (fun x => r ∣ x),
      (x - a) / r ∈ Finset.Icc (0 : ℤ) ((L : ℤ) / r) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    simp only [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by linarith) hr.le, Int.ediv_le_ediv hr (by linarith)⟩
  have hinj : Set.InjOn (fun x => (x - a) / r)
      ((Finset.Ico a (a + L)).filter (fun x => r ∣ x) : Set ℤ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨k, rfl⟩ := hx.2
    obtain ⟨m, rfl⟩ := hy.2
    simp only at hxy
    rw [show r * k - a = -a + r * k by ring, show r * m - a = -a + r * m by ring,
      Int.add_mul_ediv_left _ _ hr.ne', Int.add_mul_ediv_left _ _ hr.ne'] at hxy
    have : k = m := by linarith
    rw [this]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hq0 : 0 ≤ (L : ℤ) / r := Int.ediv_nonneg (by positivity) hr.le
  rw [Int.card_Icc, sub_zero] at hcard
  have hc : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℝ) ≤
      (((L : ℤ) / r : ℤ) : ℝ) + 1 := by
    have h1 : ((((Finset.Ico a (a + L)).filter (fun x => r ∣ x)).card : ℕ) : ℤ) ≤ (L : ℤ) / r + 1 := by
      have := Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ (L : ℤ) / r + 1)
      omega
    exact_mod_cast h1
  have hdiv : (((L : ℤ) / r : ℤ) : ℝ) ≤ (L : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hr)]
    exact_mod_cast Int.ediv_mul_le (L : ℤ) hr.ne'
  linarith

private theorem sum_range_one_div_pow_succ_eq (x : ℝ) (hx : 1 < x) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / x ^ (k + 1) = (1 - 1 / x ^ K) / (x - 1) := by
  have hx0 : x - 1 ≠ 0 := by linarith
  have hxp : x ≠ 0 := by linarith
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

theorem sum_padicValInt_le : WindowSum := by
  intro ℓ _ a L D S hS h0 hD
  have hℓ : ℓ.Prime := Fact.out
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) (by linarith)
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · have hzero : ∑ i ∈ S, padicValInt ℓ i = 0 := Finset.sum_eq_zero fun i hi =>
      (h0 ((abs_nonpos_iff.1 (by exact_mod_cast hD i hi)) ▸ hi)).elim
    rw [hzero]
    simpa [Real.logb_zero] using hL0
  have hv : ∀ i ∈ S, padicValInt ℓ i =
      ((Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    intro i hi
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)

    have hvK : padicValInt ℓ i ≤ Nat.log ℓ D := by
      have hdvd : (ℓ : ℤ) ^ padicValInt ℓ i ∣ i := (padicValInt_dvd_iff _ _).2 (Or.inr le_rfl)
      have h1 : ℓ ^ padicValInt ℓ i ∣ i.natAbs := by
        rw [← Int.natCast_dvd]
        exact_mod_cast hdvd
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hi0) h1
      have h3 : i.natAbs ≤ D := by
        have h4 := hD i hi
        rw [← Int.natCast_natAbs] at h4
        exact_mod_cast h4
      exact Nat.le_log_of_pow_le hℓ.one_lt (h2.trans h3)
    have hf : (Finset.range (Nat.log ℓ D)).filter (fun k => (ℓ : ℤ) ^ (k + 1) ∣ i) =
        Finset.range (padicValInt ℓ i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, padicValInt_dvd_iff, hi0, false_or]
      omega
    rw [hf, Finset.card_range]
  have hcount : ∀ k, ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ) ≤
      (L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1 := by
    intro k
    have h1 := windowSum_count a L ((ℓ : ℤ) ^ (k + 1)) (pow_pos (by exact_mod_cast hℓ.pos) _)
    push_cast at h1
    refine le_trans ?_ h1
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hS)
  have hsum : ∑ i ∈ S, padicValInt ℓ i = ∑ k ∈ Finset.range (Nat.log ℓ D),
      (S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card := by
    rw [Finset.sum_congr rfl hv]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlog : ((Nat.log ℓ D : ℕ) : ℝ) ≤ Real.logb ℓ D := by
    rw [Real.le_logb_iff_rpow_le hℓ1 (by exact_mod_cast hDpos), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self ℓ hDpos.ne'
  have h1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hy : 0 ≤ 1 / (ℓ : ℝ) ^ Nat.log ℓ D := by positivity
  have hgeo : (L : ℝ) * ((1 - 1 / (ℓ : ℝ) ^ Nat.log ℓ D) / ((ℓ : ℝ) - 1)) ≤
      (L : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [← mul_div_assoc, div_le_div_iff₀ h1 h1]
    nlinarith [Nat.cast_nonneg (α := ℝ) L, mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hy]
  rw [hsum]
  push_cast
  calc ∑ k ∈ Finset.range (Nat.log ℓ D), ((S.filter (fun i => (ℓ : ℤ) ^ (k + 1) ∣ i)).card : ℝ)
      ≤ ∑ k ∈ Finset.range (Nat.log ℓ D), ((L : ℝ) / (ℓ : ℝ) ^ (k + 1) + 1) :=
        Finset.sum_le_sum fun k _ => hcount k
    _ = (L : ℝ) * ∑ k ∈ Finset.range (Nat.log ℓ D), 1 / (ℓ : ℝ) ^ (k + 1) + (Nat.log ℓ D : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
        rw [sum_range_one_div_pow_succ_eq _ hℓ1]
        linarith

end Formalism.WindowSums
end
end

