module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import GroundTheory.GlobalFields.Artin.LogCharpoly

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.InversePowerBoundHolds
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace InversePowerBound

lemma sq_le_inv_pow (s : ℕ) (y : ℝ) (hy : -1 < y) (h0 : 0 ≤ 1 - (s : ℝ) * y / 2) :
    (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((1 + y) ^ s)⁻¹ := by
  have h1 : 0 < 1 + y := by linarith
  have hpos : 0 < (1 + y) ^ s := pow_pos h1 s

  have hA : 1 - (s : ℝ) * y / 2 ≤ Real.exp (-((s : ℝ) * y / 2)) := by
    linarith [Real.add_one_le_exp (-((s : ℝ) * y / 2))]
  have hB : (1 + y) ^ s ≤ Real.exp ((s : ℝ) * y) := by
    calc (1 + y) ^ s ≤ (Real.exp y) ^ s :=
          pow_le_pow_left₀ h1.le (by linarith [Real.add_one_le_exp y]) s
      _ = Real.exp ((s : ℝ) * y) := by rw [← Real.exp_nat_mul]
  have hC : (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := by
    calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ (Real.exp (-((s : ℝ) * y / 2))) ^ 2 :=
          pow_le_pow_left₀ h0 hA 2
      _ = Real.exp (-((s : ℝ) * y)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := hC
    _ = (Real.exp ((s : ℝ) * y))⁻¹ := by rw [Real.exp_neg]
    _ ≤ ((1 + y) ^ s)⁻¹ := inv_anti₀ hpos hB

end InversePowerBound

theorem inverse_power_bound_holds : A10 := by
  intro s _hs
  refine ⟨(s : ℝ) ^ 4 / 16, by positivity, fun y hy => ?_⟩
  have hpos : 0 < ((1 + y) ^ s)⁻¹ := inv_pos.mpr (pow_pos (by linarith) s)

  have hsq : 1 - (s : ℝ) * y + (s : ℝ) ^ 2 / 4 * y ^ 2 = (1 - (s : ℝ) * y / 2) ^ 2 := by ring
  have e : (s : ℝ) ^ 4 / 16 * y ^ 4 = ((s : ℝ) * y / 2) ^ 4 := by ring
  by_cases h0 : 0 ≤ 1 - (s : ℝ) * y / 2
  · have h := InversePowerBound.sq_le_inv_pow s y hy h0
    have : 0 ≤ (s : ℝ) ^ 4 / 16 * y ^ 4 := by positivity
    linarith
  ·
    rw [not_le] at h0
    have hu : 1 < (s : ℝ) * y / 2 := by linarith
    have k1 : (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
    have k2 : ((s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 4 := by
      have : 1 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
      nlinarith
    linarith

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KFiniteInclusion
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace WeightedEigenSum

theorem pow_eig {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (m : ℝ) (x : V)
    (h : T x = (m : ℂ) • x) (s : ℕ) : ((1 + T) ^ s) x = (((1 + m) ^ s : ℝ) : ℂ) • x := by
  induction s with
  | zero => simp
  | succ k ih =>
    have hx : x + (m : ℂ) • x = (((1 + m : ℝ)) : ℂ) • x := by
      push_cast
      rw [add_smul, one_smul]
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.add_apply, Module.End.one_apply, h, hx,
      smul_smul]
    congr 1
    push_cast
    ring

theorem wsum_le {ι : Type} (μ : ι → ℝ) (hnn : ∀ i, 0 ≤ μ i) (hfin : ∀ R : ℝ, {i | μ i ≤ R}.Finite)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : ℕ) (hs : 1 ≤ s) (K : ℝ)
    (hS : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) → ∑ i ∈ S, phiR s R (μ i) * a i ≤ K ^ 2)
    (T : Finset ι) : ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i ≤ K ^ 2 := by
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ i ∈ T, μ i < R0 :=
    ⟨∑ i ∈ T, μ i + 1, fun i hi => by
      have := Finset.single_le_sum (fun j _ => hnn j) hi
      linarith⟩
  have key : ∀ R : ℝ, R0 ≤ R →
      ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i ≤ K ^ 2 := by
    intro R hR
    have hSmem : ∀ i, i ∈ (hfin R).toFinset.filter (fun i => μ i < R) ↔ μ i < R := by
      intro i
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
    have hTS : T ⊆ (hfin R).toFinset.filter (fun i => μ i < R) :=
      fun i hi => (hSmem i).mpr (lt_of_lt_of_le (hR0 i hi) hR)
    have h1 := hS R _ hSmem
    have h2 : ∑ i ∈ T, phiR s R (μ i) * a i ≤
        ∑ i ∈ (hfin R).toFinset.filter (fun i => μ i < R), phiR s R (μ i) * a i :=
      Finset.sum_le_sum_of_subset_of_nonneg hTS (fun i _ _ => mul_nonneg (le_max_right _ _) (ha i))
    have h3 : ∑ i ∈ T, phiR s R (μ i) * a i =
        ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hlt : ((1 + R) ^ s)⁻¹ ≤ ((1 + μ i) ^ s)⁻¹ := by
        apply inv_anti₀ (pow_pos (by linarith [hnn i]) s)
        exact pow_le_pow_left₀ (by linarith [hnn i]) (by linarith [hR0 i hi]) s
      rw [phiR, max_eq_left (by linarith)]
      ring
    linarith
  have hpow : Filter.Tendsto (fun R : ℝ => (1 + R) ^ s) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by omega : s ≠ 0)).comp
      (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
  have ht : Filter.Tendsto
      (fun R : ℝ => ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i) Filter.atTop
      (nhds (∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - 0 * ∑ i ∈ T, a i)) :=
    tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp hpow).mul_const _)
  have hlim := le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨R0, key⟩)
  simpa using hlim

end WeightedEigenSum

theorem eigen_weighted_sum_bound : A0 → FunctionalCalculusLaws → B5 := by
  intro _ _ n ε V _ _ E _ ι b μ hb f s K hK hS hs v
  have hv : v = ∑ i ∈ (b.repr v).support, b.repr v i • b i := by
    conv_lhs => rw [← b.linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hpos : ∀ i, 0 < (1 + μ i) ^ s := fun i => pow_pos (by linarith [hb.nonneg i]) s
  have heig : ∀ i, ((1 + casimirK ε E) ^ s) (b i) = (((1 + μ i) ^ s : ℝ) : ℂ) • b i :=
    fun i => WeightedEigenSum.pow_eig _ (μ i) (b i) (hb.eig i) s
  have hw : ((1 + casimirK ε E) ^ s) v =
      ∑ i ∈ (b.repr v).support, (b.repr v i * (((1 + μ i) ^ s : ℝ) : ℂ)) • b i := by
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig, smul_smul]
  have hfv : f v = inner ℂ (∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i) (((1 + casimirK ε E) ^ s) v) := by
    rw [hw, hb.on.inner_sum]
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    have h1 : ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ) * (((1 + μ i) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    linear_combination (-(b.repr v i * f (b i))) * h1
  have hu2 : ‖∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 ≤ K ^ 2 := by
    have e : ‖∑ i ∈ (b.repr v).support,
        (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 =
        ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [@norm_sq_eq_re_inner ℂ, hb.on.inner_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_conj, mul_pow]
    have e2 : ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 ≤
        ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h0 : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      have h1 : ((1 + μ i) ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hb.nonneg i]))
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖f (b i)‖) h0) (sub_nonneg.mpr h1)]
    have e3 : ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 ≤ K ^ 2 :=
      WeightedEigenSum.wsum_le μ hb.nonneg hb.fin (fun i => ‖f (b i)‖ ^ 2) (fun i => sq_nonneg _) s hs K hS _
    linarith
  have hu := (pow_le_pow_iff_left₀ (norm_nonneg _) hK two_ne_zero).mp hu2
  rw [hfv]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionSingle
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SecondMomentAlgebra

lemma alg (n m : ℕ) (C1 C2 s T : ℝ) (hn : (1:ℝ) ≤ n) (hm : 1 ≤ m) (hC2 : 0 < C2) (hs : 1 ≤ s)
    (hs2 : 2 * C1 * (2 * (n:ℝ)) ^ m ≤ s)
    (h : (s ^ 2 / (2 * n)) ^ m ≤ C1 * s ^ (2 * m - 1) + C2 * s ^ (2 * m - 2) * T) :
    1 / (2 * (2 * (n:ℝ)) ^ m * C2) * s ^ 2 ≤ T := by
  have hA : 0 < (2 * (n:ℝ)) ^ m := by positivity
  have hs0 : 0 < s := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [e1, e2, div_pow, ← pow_mul] at h
  set A := (2 * (n:ℝ)) ^ (k + 1) with hAdef
  have hP : 0 < s ^ (2 * k) := by positivity
  have f1 : s ^ (2 * (k + 1)) = s ^ (2 * k) * s ^ 2 := by ring
  have f2 : s ^ (2 * k + 1) = s ^ (2 * k) * s := by ring
  rw [f1, f2, div_le_iff₀ hA] at h
  have h' : s ^ (2 * k) * s ^ 2 ≤ s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by
    calc s ^ (2 * k) * s ^ 2 ≤ (C1 * (s ^ (2 * k) * s) + C2 * s ^ (2 * k) * T) * A := h
      _ = s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by ring
  have h'' : s ^ 2 ≤ A * C1 * s + A * C2 * T := le_of_mul_le_mul_left h' hP
  have h2 : 2 * (A * C1 * s) ≤ s ^ 2 := by
    have := mul_le_mul_of_nonneg_right hs2 hs0.le
    nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma reEig (v : V) (μ : ℝ) : (inner ℂ v ((μ:ℂ) • v)).re = μ * ‖v‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, pow_two]

lemma cs {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, f c d) ^ 2 ≤ ((n:ℝ) * n) * ∑ c, ∑ d, f c d ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n × Fin n))) (f := fun p => f p.1 p.2)
  simpa [Fintype.sum_prod_type', Fintype.sum_prod_type, Finset.card_univ] using h

lemma zsum {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hZc : ∀ a b, ε a = ε b → Z ε E a b = 0) (w : V) :
    ∑ c, ∑ d, ‖Z ε E c d w‖ ^ 2 = ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 w‖ ^ 2 := by
  rw [← Fintype.sum_prod_type' (fun c d => ‖Z ε E c d w‖ ^ 2), nc, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · rfl
  · simp [hZc _ _ (not_not.mp h)]

lemma scale {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) (hv : v ≠ 0) :
    ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2 =
      ‖v‖ ^ 2 * ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 (((‖v‖ : ℂ)⁻¹) • v)‖ ^ 2 := by
  have h0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm, mul_pow, ← Finset.mul_sum]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]

end SecondMomentAlgebra

set_option maxHeartbeats 800000 in
theorem second_moment_of_columns : A0 → A1 → FiltrationAdjointStable → CasimirIsRealScalar → A5 → A6 → ColumnOperatorMoments → A8 := by
  intro h0 h1 h1s h3c h5 h6 h8a n ε V _ _ E hM
  obtain ⟨-, -, hZc, hcas⟩ := h0 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3c n ε V E hM
  set m : ℕ := 2 ^ n with hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  have hnm : n ≤ m := Nat.lt_two_pow_self.le
  have h5' := h5 n ε V E hM m hm1 hnm
  choose u hu w hw hdec using fun e : Fin n => h5' e e
  have hadj : ∀ e c d, ∃ w' ∈ U E (2 * m - 2), ∀ x y : V,
      inner ℂ x (w e c d y) = inner ℂ (w' x) y := fun e c d => h1s n ε V E hM _ _ (hw e c d)
  choose w' hw' hadj using hadj
  have bu : ∀ e, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖u e v‖ ≤ C * √(1 + μ) ^ (2 * m - 1) * ‖v‖ := fun e => h6 n ε V E hM _ _ (hu e)
  choose Cu hCu0 hCu using bu
  have bw : ∀ e c d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖w' e c d v‖ ≤ C * √(1 + μ) ^ (2 * m - 2) * ‖v‖ := fun e c d => h6 n ε V E hM _ _ (hw' e c d)
  choose Cw hCw0 hCw using bw
  set C1 : ℝ := ∑ e, Cu e with hC1def
  set C2 : ℝ := ∑ e, ∑ c, ∑ d, Cw e c d + 1 with hC2def
  have hC1e : ∀ e, Cu e ≤ C1 := fun e =>
    Finset.single_le_sum (f := Cu) (fun i _ => hCu0 i) (Finset.mem_univ e)
  have hC2e : ∀ e c d, Cw e c d ≤ C2 := by
    intro e c d
    have a1 : Cw e c d ≤ ∑ d', Cw e c d' :=
      Finset.single_le_sum (f := fun d' => Cw e c d') (fun i _ => hCw0 e c i) (Finset.mem_univ d)
    have a2 : ∑ d', Cw e c d' ≤ ∑ c', ∑ d', Cw e c' d' :=
      Finset.single_le_sum (f := fun c' => ∑ d', Cw e c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => hCw0 e i j)) (Finset.mem_univ c)
    have a3 : ∑ c', ∑ d', Cw e c' d' ≤ ∑ e', ∑ c', ∑ d', Cw e' c' d' :=
      Finset.single_le_sum (f := fun e' => ∑ c', ∑ d', Cw e' c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
        (Finset.mem_univ e)
    linarith
  have hC2 : 0 < C2 := by
    have : 0 ≤ ∑ e, ∑ c, ∑ d, Cw e c d :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
    linarith
  set N : ℝ := (2 * (n:ℝ)) ^ m with hNdef
  refine ⟨1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1), max (max 1 (|κ| + 1)) ((2 * C1 * N) ^ 2),
    by positivity, ?_⟩
  intro μ v hμ hv
  have hμ1 : 1 ≤ μ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hμ
  have hμκ : |κ| + 1 ≤ μ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hμ
  have hμC : (2 * C1 * N) ^ 2 ≤ μ := le_trans (le_max_right _ _) hμ
  by_cases hv0 : v = 0
  · subst hv0
    simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set v1 : V := ((‖v‖ : ℂ)⁻¹) • v with hv1def
  have hv1n : ‖v1‖ = 1 := by
    rw [hv1def, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hv1E : Eig ε E μ v1 := by
    have hv' : casimirK ε E v = (μ : ℂ) • v := hv
    show casimirK ε E (((‖v‖ : ℂ)⁻¹) • v) = (μ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v)
    rw [map_smul, hv', smul_comm]
  rw [SecondMomentAlgebra.scale ε E v hv0]
  suffices hS : 1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1) * (1 + μ) ^ 2 ≤
      ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v1‖ ^ 2 by
    have := mul_le_mul_of_nonneg_left hS (sq_nonneg ‖v‖)
    linarith
  have hX : ∑ a, ∑ b, ‖E a b v1‖ ^ 2 = 2 * μ - κ := by
    rw [(hcas κ hκ v1).1, show casimirK ε E v1 = (μ : ℂ) • v1 from hv1E, SecondMomentAlgebra.reEig, hv1n]
    ring
  have hpos : 0 < 2 * μ - κ := by linarith [le_abs_self κ]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hX
    simp at hX
    linarith
  obtain ⟨e0, -⟩ := hne
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Fin.pos e0)
  have hnr : (n:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN : 0 < N := by positivity
  obtain ⟨e, -, he⟩ := exists_le_of_sum_le (s := Finset.univ) ⟨e0, Finset.mem_univ _⟩
    (f := fun _ => (2 * μ - κ) / n) (g := fun e => ∑ a, ‖E a e v1‖ ^ 2) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (n:ℝ) * ((2 * μ - κ) / n) = 2 * μ - κ := by field_simp
      rw [this, ← hX, Finset.sum_comm])
  have h8 := h8a n ε V E hM v1 hv1n e n
  rw [hdec e] at h8
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, inner_add_right, inner_sum,
    Complex.add_re, Complex.re_sum] at h8
  have hs : √(1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
  have b1 : (inner ℂ v1 (u e v1)).re ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
    have r := re_inner_le_norm (𝕜 := ℂ) v1 (u e v1)
    have r2 : ‖u e v1‖ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
      simpa [hv1n] using hCu e μ v1 (by linarith) hv1E
    rw [hv1n, one_mul] at r
    exact le_trans r r2
  have b2 : ∀ c d, (inner ℂ v1 (w e c d (Z ε E c d v1))).re ≤
      C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ := by
    intro c d
    rw [hadj e c d]
    have r := re_inner_le_norm (𝕜 := ℂ) (w' e c d v1) (Z ε E c d v1)
    have r2 : ‖w' e c d v1‖ ≤ C2 * √(1 + μ) ^ (2 * m - 2) := by
      have := hCw e c d μ v1 (by linarith) hv1E
      rw [hv1n, mul_one] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (hC2e e c d) (by positivity))
    exact le_trans r (mul_le_mul_of_nonneg_right r2 (norm_nonneg _))
  have hsum : ∑ c, ∑ d, ‖Z ε E c d v1‖ ≤ √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt (SecondMomentAlgebra.cs (fun c d => ‖Z ε E c d v1‖)))
  set T := √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) with hTdef
  have hXe : √(1 + μ) ^ 2 / (2 * n) ≤ ∑ a, ‖E a e v1‖ ^ 2 := by
    rw [hs]
    calc (1 + μ) / (2 * n) ≤ (2 * μ - κ) / n := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [le_abs_self κ]
      _ ≤ _ := he
  have hmain : (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤
      C1 * √(1 + μ) ^ (2 * m - 1) + C2 * √(1 + μ) ^ (2 * m - 2) * T := by
    calc (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤ (∑ a, ‖E a e v1‖ ^ 2) ^ m :=
          pow_le_pow_left₀ (by positivity) hXe m
      _ ≤ _ := h8
      _ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) + ∑ c, ∑ d, C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ :=
          add_le_add b1 (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => b2 c d)
      _ ≤ _ := by
          simp_rw [← Finset.mul_sum]
          exact add_le_add (mul_le_mul_of_nonneg_right (hC1e e) (by positivity))
            (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hs1 : 1 ≤ √(1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have hs2 : 2 * C1 * N ≤ √(1 + μ) := by
    refine le_trans (le_abs_self _) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have key := SecondMomentAlgebra.alg n m C1 C2 (√(1 + μ)) T hn1 hm1 hC2 hs1 hs2 hmain
  rw [hs] at key
  have hS'0 : 0 ≤ ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by positivity
  have hq : (1 / (2 * N * C2) * (1 + μ)) ^ 2 ≤ (n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) key 2
    rwa [hTdef, Real.sq_sqrt (by positivity)] at this
  have hq' : (1 + μ) ^ 2 ≤ (2 * N * C2) ^ 2 * ((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) := by
    have e3 : (1 + μ) ^ 2 = (2 * N * C2) ^ 2 * (1 / (2 * N * C2) * (1 + μ)) ^ 2 := by
      field_simp
    rw [e3]
    exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
  rw [← SecondMomentAlgebra.zsum ε E hZc v1]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hS'0 (sq_nonneg (2 * N * C2))]

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.NilpotentOfPowerTraces
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CharpolyPowerTraces

open Polynomial

theorem coeff_succ {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) :
    ((m : R) + 1) * N.charpolyRev.coeff (m + 1) = 0 := by
  have hps : (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h]
  have hd : derivative N.charpolyRev = 0 := by
    have hc := GroundTheory.Global.coe_derivative_charpolyRev N
    rw [hps, mul_zero] at hc
    exact Polynomial.coe_eq_zero_iff.mp hc
  have hm := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hm
  rw [mul_comm]
  exact hm

theorem coeff_succ_zero {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) : N.charpolyRev.coeff (m + 1) = 0 := by
  have hu : IsUnit ((m : R) + 1) := by
    have : ((m : R) + 1) = algebraMap ℚ R ((m : ℚ) + 1) := by simp
    rw [this]; exact (IsUnit.mk0 _ (by positivity)).map _
  exact hu.mul_right_eq_zero.mp (coeff_succ N h m)

theorem charpoly_eq {R : Type} [CommRing R] [Algebra ℚ R] [Nontrivial R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (h : ∀ k, (N ^ (k + 1)).trace = 0) : N.charpoly = X ^ n := by
  have hRev : ∀ i, 1 ≤ i → N.charpolyRev.coeff i = 0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    exact coeff_succ_zero N h m
  have hdeg : N.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  ext j
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy j n with hj | hj | hj
  · rw [if_neg hj.ne]
    have hz := hRev (n - j) (by omega)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, hdeg,
      Polynomial.revAt_le (by omega)] at hz
    rwa [show n - (n - j) = j by omega] at hz
  · rw [if_pos hj]
    have hl := (Matrix.charpoly_monic N).leadingCoeff
    rw [Polynomial.leadingCoeff, hdeg] at hl
    rw [hj]
    exact hl
  · rw [if_neg hj.ne']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end CharpolyPowerTraces

theorem nilpotent_of_power_traces : A4 := by
  unfold A4
  intro R _ _ n N h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hc := Matrix.aeval_self_charpoly N
  rw [CharpolyPowerTraces.charpoly_eq N h, Polynomial.aeval_X_pow] at hc
  exact hc

end PositivityTheory.CW

end
end

