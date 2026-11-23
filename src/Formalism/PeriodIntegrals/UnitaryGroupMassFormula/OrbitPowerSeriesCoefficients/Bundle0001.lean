module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.ExpSum
section
noncomputable section

open Classical

namespace PI.OrbShared.ExpSum

open MvPowerSeries

variable {K : Type*} [Field K] [CharZero K]

abbrev eS {τ : Type*} (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  PowerSeries.subst f (PowerSeries.exp K)

theorem fin_two_vector_eq_matrixVecCons (e : Fin 2 →₀ ℕ) (k j : ℕ) :
    e = Finsupp.single 0 k + Finsupp.single 1 j ↔ e 0 = k ∧ e 1 = j := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

theorem coeff_X_add_X_pow (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : K) else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1), coeff e ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (n - m) *
      (n.choose m : MvPowerSeries (Fin 2) K)) = if e 0 = m ∧ e 1 = n - m then (n.choose m : K) else 0 := by
    intro m _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, X_pow_eq, X_pow_eq, monomial_mul_monomial, coeff_monomial,
      mul_one, nsmul_eq_mul]
    simp only [fin_two_vector_eq_matrixVecCons]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h
  · rw [Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hb h1.symm
    · intro hb
      exfalso
      apply hb
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [Finset.mem_range] at hm
    omega

theorem coeff_exp_K (n : ℕ) : PowerSeries.coeff n (PowerSeries.exp K) = ((n.factorial : K))⁻¹ := by
  simp [PowerSeries.coeff_exp]

private lemma coeff_eS_X (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    coeff e (eS (X i : MvPowerSeries (Fin 2) K)) =
      if e = Finsupp.single i (e i) then ((e i).factorial : K)⁻¹ else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp only [coeff_X_pow, coeff_exp_K, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro h'
      apply hd
      rw [h']
      simp
  · apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp

theorem eS_X_add_X : eS (X 0 + X 1 : MvPowerSeries (Fin 2) K) = eS (X 0) * eS (X 1) := by
  ext e
  have hL : coeff e (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) =
      ((e 0 + e 1).factorial : K)⁻¹ * ((e 0 + e 1).choose (e 0) : K) := by
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    rw [finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_exp_K, coeff_X_add_X_pow, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_X_add_X_pow, if_neg (fun h => hd h.symm), smul_zero]
  rw [hL, MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
  · rw [coeff_eS_X, coeff_eS_X, if_pos (by simp), if_pos (by simp)]
    simp only [Finsupp.single_eq_same]
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : ((e 0 + e 1).choose (e 0) : K) * (e 0).factorial * (e 1).factorial =
        (e 0 + e 1).factorial := by exact_mod_cast h1
    have f0 : ((e 0).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have f1 : ((e 1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hC : ((e 0 + e 1).choose (e 0) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    rw [← h2]
    field_simp
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_eS_X, coeff_eS_X]
    by_cases h1 : p1 = Finsupp.single 0 (p1 0)
    · by_cases h2 : p2 = Finsupp.single 1 (p2 1)
      · exfalso
        apply hne
        have e0 : e 0 = p1 0 := by
          rw [← hp, Finsupp.add_apply, h2]
          simp
        have e1 : e 1 = p2 1 := by
          rw [← hp, Finsupp.add_apply, h1]
          simp
        rw [h1, h2, e0, e1]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_vector_eq_matrixVecCons e (e 0) (e 1)).mpr ⟨rfl, rfl⟩).symm) h

variable {τ υ : Type*}

theorem subst_psubst {b : τ → MvPowerSeries υ K} (hb : HasSubst b) {a : MvPowerSeries τ K}
    (ha : PowerSeries.HasSubst a) (φ : PowerSeries K) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb]

theorem eS_add (f g : MvPowerSeries τ K) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    eS (f + g) = eS f * eS g := by
  let b : Fin 2 → MvPowerSeries τ K := ![f, g]
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i <;> simp [b, hf, hg]
  have h1 : subst b (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) = eS (f + g) := by
    rw [subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_add hb, subst_X hb,
      subst_X hb]
    rfl
  have h2 : subst b (eS (X 0 : MvPowerSeries (Fin 2) K) * eS (X 1)) = eS f * eS g := by
    rw [subst_mul hb, subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
      subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_X hb, subst_X hb]
    rfl
  rw [← h1, eS_X_add_X, h2]

theorem eS_zero : eS (0 : MvPowerSeries τ K) = 1 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]
  · simp [coeff_exp_K]
  · intro d hd
    simp [zero_pow hd]

theorem eS_sum {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries τ K)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) : eS (∑ i ∈ s, f i) = ∏ i ∈ s, eS (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact eS_zero
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      eS_add _ _ (hf a (Finset.mem_insert_self a s)) ?_,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => hf i (Finset.mem_insert_of_mem hi)

theorem subst_eS {b : τ → MvPowerSeries υ K} (hb : HasSubst b) (f : MvPowerSeries τ K)
    (hf : constantCoeff f = 0) : subst b (eS f) = eS (subst b f) := by
  exact subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero hf) _

end PI.OrbShared.ExpSum

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.KillSubst
section
noncomputable section

namespace PI.OrbShared

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {σ τ υ R : Type*} [CommRing R]

theorem hasSubst_killCompl (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    HasSubst (fun s => killCompl e (a s)) where
  const_coeff s := by
    have h : constantCoeff (killCompl e (a s)) = constantCoeff (a s) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
        coeff_killCompl, Finsupp.embDomain_zero]
    rw [h]; exact ha.const_coeff s
  coeff_zero d := by
    refine (ha.coeff_zero (Finsupp.embDomain e d)).subset ?_
    intro s hs
    simpa [coeff_killCompl] using hs

theorem continuous_killCompl [UniformSpace R] [DiscreteUniformity R] (e : υ ↪ τ) :
    Continuous (killCompl (R := R) e : MvPowerSeries τ R → MvPowerSeries υ R) := by
  apply continuous_pi
  intro x
  have : (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p := by
    funext p; exact coeff_killCompl p x
  rw [this]
  exact WithPiTopology.continuous_coeff R _

theorem killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hb := hasSubst_killCompl e ha
  rw [comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]

theorem killCompl_eq_subst (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by
  have := killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f
  rw [subst_self] at this
  exact this

end PI.OrbShared
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.SolvableEquivalenceOfBaseChange
section
noncomputable section

open Classical

namespace PI.OrbShared.Tri

open MvPowerSeries Finsupp

variable {K : Type*} [Field K] {σ : Type*} [Finite σ]

def IsTri (c : K) (a : σ → MvPowerSeries σ K) : Prop :=
  ∀ v (n : σ →₀ ℕ), n.degree ≤ 1 → coeff n (a v) = if n = single v 1 then c else 0

def P (a : σ → MvPowerSeries σ K) (d : σ →₀ ℕ) : MvPowerSeries σ K := d.prod fun s e => (a s) ^ e

variable {c : K} {a : σ → MvPowerSeries σ K}

theorem IsTri.constantCoeff (ha : IsTri c a) (v : σ) : constantCoeff (a v) = 0 := by
  have h := ha v 0 (by simp)
  rw [← coeff_zero_eq_constantCoeff_apply, h, if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero))]

theorem IsTri.hasSubst (ha : IsTri c a) : HasSubst a :=
  hasSubst_of_constantCoeff_zero fun v => ha.constantCoeff v

theorem ord_mul {f g : MvPowerSeries σ K} {m n : ℕ} (hf : (m : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) :
    ((m + n : ℕ) : ℕ∞) ≤ (f * g).order := by
  push_cast
  exact (add_le_add hf hg).trans le_order_mul

theorem ord_add {f g : MvPowerSeries σ K} {n : ℕ} (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) :
    (n : ℕ∞) ≤ (f + g).order :=
  (le_min hf hg).trans min_order_le_add

theorem ord_pow {f : MvPowerSeries σ K} (hf : 1 ≤ f.order) (n : ℕ) : (n : ℕ∞) ≤ (f ^ n).order := by
  refine le_trans ?_ (le_order_pow n)
  have := nsmul_le_nsmul_right hf n
  simpa using this

theorem ord_pow_sub {x y : MvPowerSeries σ K} (hx : 1 ≤ x.order) (hy : 1 ≤ y.order)
    (hxy : ((2 : ℕ) : ℕ∞) ≤ (y - x).order) (n : ℕ) : ((n + 1 : ℕ) : ℕ∞) ≤ (y ^ n - x ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show y ^ (n + 1) - x ^ (n + 1) = y ^ n * (y - x) + (y ^ n - x ^ n) * x by ring]
    apply ord_add
    · have := ord_mul (ord_pow hy n) hxy
      exact le_trans (by norm_cast) this
    · have := ord_mul ih (n := 1) (by simpa using hx)
      exact le_trans (by norm_cast) this

theorem ord_prod_sub {ι : Type*} (S : Finset ι) (x y : ι → MvPowerSeries σ K) (d : ι → ℕ)
    (hx : ∀ i, 1 ≤ (x i).order) (hy : ∀ i, 1 ≤ (y i).order)
    (hxy : ∀ i, ((2 : ℕ) : ℕ∞) ≤ (y i - x i).order) :
    ((∑ i ∈ S, d i : ℕ) : ℕ∞) ≤ (∏ i ∈ S, x i ^ d i).order ∧
      ((∑ i ∈ S, d i + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    refine ⟨ord_mul (ord_pow (hx j) _) ih.1, ?_⟩
    rw [show y j ^ d j * ∏ i ∈ S, y i ^ d i - x j ^ d j * ∏ i ∈ S, x i ^ d i =
      y j ^ d j * (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i) +
        (y j ^ d j - x j ^ d j) * ∏ i ∈ S, x i ^ d i by ring]
    apply ord_add
    · have := ord_mul (ord_pow (hy j) (d j)) ih.2
      exact le_trans (by norm_cast) this
    · have := ord_mul (ord_pow_sub (hx j) (hy j) (hxy j) (d j)) ih.1
      exact le_trans (by norm_cast <;> omega) this

theorem prod_CX (d : σ →₀ ℕ) :
    (d.prod fun s e => (C c * X s : MvPowerSeries σ K) ^ e) = monomial d (c ^ d.degree) := by
  classical
  have key : ∀ S : Finset σ, (∏ s ∈ S, (C c * X s : MvPowerSeries σ K) ^ d s) =
      monomial (∑ s ∈ S, single s (d s)) (c ^ (∑ s ∈ S, d s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.prod_insert hj, ih, Finset.sum_insert hj, Finset.sum_insert hj, mul_pow, X_pow_eq,
        ← map_pow, ← monomial_zero_eq_C_apply, monomial_mul_monomial, monomial_mul_monomial, zero_add,
        mul_one, pow_add]
  have hs : (∑ s ∈ d.support, single s (d s)) = d := Finsupp.sum_single d
  rw [Finsupp.prod, key, hs]
  rfl

theorem IsTri.order_one (ha : IsTri c a) (v : σ) : 1 ≤ (a v).order :=
  one_le_order_iff_constCoeff_eq_zero.mpr (ha.constantCoeff v)

theorem IsTri.order_sub (ha : IsTri c a) (v : σ) : ((2 : ℕ) : ℕ∞) ≤ (a v - C c * X v).order := by
  refine le_order fun n hn => ?_
  have hn' : n.degree ≤ 1 := by
    have : (n.degree : ℕ∞) < ((2 : ℕ) : ℕ∞) := hn
    norm_cast at this
    omega
  rw [map_sub, ha v n hn', coeff_C_mul, coeff_X]
  split_ifs <;> simp

theorem coeff_P_of_le (ha : IsTri c a) (d e : σ →₀ ℕ) (he : e.degree ≤ d.degree) :
    coeff e (P a d) = if e = d then c ^ d.degree else 0 := by
  have hX : ∀ v, 1 ≤ (C c * X v : MvPowerSeries σ K).order := fun v =>
    one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
  have h := (ord_prod_sub d.support (fun v => C c * X v) a d hX ha.order_one ha.order_sub).2
  have h0 : coeff e (P a d - d.prod fun s e => (C c * X s : MvPowerSeries σ K) ^ e) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    have : (∑ i ∈ d.support, d i) = d.degree := rfl
    rw [this]
    exact_mod_cast Nat.lt_succ_of_le he
  rw [map_sub, prod_CX, coeff_monomial, sub_eq_zero] at h0
  exact h0

theorem coeff_subst_tri (ha : IsTri c a) (F : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    coeff e (subst a F) = c ^ e.degree * coeff e F +
      ∑ᶠ d, if d.degree < e.degree then coeff d F * coeff e (P a d) else 0 := by
  rw [coeff_subst ha.hasSubst]
  have hterm : ∀ d : σ →₀ ℕ, coeff d F • coeff e (d.prod fun s e => (a s) ^ e) =
      (if d = e then c ^ e.degree * coeff e F else 0) +
        (if d.degree < e.degree then coeff d F * coeff e (P a d) else 0) := by
    intro d
    change coeff d F * coeff e (P a d) = _
    rcases lt_trichotomy d.degree e.degree with hlt | heq | hgt
    · have hne : d ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      rw [if_neg hne, if_pos hlt, zero_add]
    · rw [if_neg (show ¬ d.degree < e.degree by rw [heq]; exact lt_irrefl _), add_zero,
        coeff_P_of_le ha d e heq.ge]
      by_cases hde : d = e
      · subst hde; simp [mul_comm]
      · rw [if_neg hde, if_neg (Ne.symm hde), mul_zero]
    · have hne : d ≠ e := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
      rw [if_neg hne, if_neg (not_lt.mpr hgt.le), coeff_P_of_le ha d e hgt.le, if_neg (Ne.symm hne)]
      simp
  simp_rw [hterm]
  rw [finsum_add_distrib]
  · rw [finsum_eq_single _ e (fun d hd => if_neg hd), if_pos rfl]
  · apply Set.Finite.subset (Set.finite_singleton e)
    intro d hd
    by_contra h
    exact hd (if_neg h)
  · apply Set.Finite.subset (Finsupp.finite_of_degree_lt e.degree)
    intro d hd
    by_contra h
    exact hd (if_neg h)

theorem vanish_of_subst (hc : c ≠ 0) (ha : IsTri c a) (F : MvPowerSeries σ K) (n : ℕ)
    (h : ∀ m : σ →₀ ℕ, m.degree < n → coeff m (subst a F) = 0) :
    ∀ m : σ →₀ ℕ, m.degree < n → coeff m F = 0 := by
  have key : ∀ k, ∀ m : σ →₀ ℕ, m.degree = k → k < n → coeff m F = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro m hm hk
      have h1 := h m (hm ▸ hk)
      rw [coeff_subst_tri ha] at h1
      have h2 : (∑ᶠ d, if d.degree < m.degree then coeff d F * coeff m (P a d) else 0) = 0 := by
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        split_ifs with hd
        · rw [ih d.degree (hm ▸ hd) d rfl (lt_trans (hm ▸ hd) hk), zero_mul]
        · rfl
      rw [h2, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc)
  exact fun m hm => key _ m rfl hm

def solvable_equivalence_of_base_change (c : K) (a : σ → MvPowerSeries σ K) (G : MvPowerSeries σ K) : ℕ → (σ →₀ ℕ) → K
  | 0 => fun _ => 0
  | k + 1 => fun m => if m.degree = k then
      (c ^ k)⁻¹ * (coeff m G - ∑ᶠ d, if d.degree < k then solvable_equivalence_of_base_change c a G k d * coeff m (P a d) else 0)
    else solvable_equivalence_of_base_change c a G k m

def sol (c : K) (a : σ → MvPowerSeries σ K) (G : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun m => solvable_equivalence_of_base_change c a G (m.degree + 1) m

theorem triangular_solution_stable (G : MvPowerSeries σ K) :
    ∀ k (m : σ →₀ ℕ), m.degree < k → solvable_equivalence_of_base_change c a G k m = solvable_equivalence_of_base_change c a G (m.degree + 1) m := by
  intro k
  induction k with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero _)
  | succ k ih =>
    intro m hm
    by_cases hk : m.degree = k
    · rw [hk]
    · have hlt : m.degree < k := by omega
      show (if m.degree = k then _ else solvable_equivalence_of_base_change c a G k m) = _
      rw [if_neg hk, ih m hlt]

theorem subst_sol (hc : c ≠ 0) (ha : IsTri c a) (G : MvPowerSeries σ K) : subst a (sol c a G) = G := by
  ext m
  rw [coeff_subst_tri ha]
  have hsol : ∀ d : σ →₀ ℕ, coeff d (sol c a G) = solvable_equivalence_of_base_change c a G (d.degree + 1) d := fun d => rfl
  have hS : (∑ᶠ d, if d.degree < m.degree then coeff d (sol c a G) * coeff m (P a d) else 0) =
      ∑ᶠ d, if d.degree < m.degree then solvable_equivalence_of_base_change c a G m.degree d * coeff m (P a d) else 0 := by
    apply finsum_congr
    intro d
    split_ifs with hd
    · rw [hsol, triangular_solution_stable G m.degree d hd]
    · rfl
  rw [hS, hsol, solvable_equivalence_of_base_change.eq_2]
  beta_reduce
  rw [if_pos rfl, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul, sub_add_cancel]

end PI.OrbShared.Tri

end
end

