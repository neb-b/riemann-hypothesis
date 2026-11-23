module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesTransport
section
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Matrix

section Cz

variable {L : Type} [Field L]

theorem cz_neg (f : PowerSeries L) {k : ℤ} (hk : k < 0) : cz f k = 0 := by
  simp [cz, not_le.mpr hk]

theorem cz_nat (f : PowerSeries L) (k : ℕ) : cz f (k : ℤ) = PowerSeries.coeff k f := by
  simp [cz]

theorem cz_add (f g : PowerSeries L) (k : ℤ) : cz (f + g) k = cz f k + cz g k := by
  unfold cz; split_ifs <;> simp

theorem cz_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries L) (k : ℤ) :
    cz (∑ i ∈ s, f i) k = ∑ i ∈ s, cz (f i) k := by
  unfold cz; split_ifs <;> simp

theorem cz_C_mul (c : L) (f : PowerSeries L) (k : ℤ) : cz (PowerSeries.C c * f) k = c * cz f k := by
  unfold cz; split_ifs <;> simp

theorem cz_rescale (c : L) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.rescale c f) k = c ^ k * cz f k := by
  rcases lt_or_ge k 0 with h | h
  · simp [cz_neg _ h]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [cz_nat, PowerSeries.coeff_rescale]

theorem cz_X_pow_mul (w : ℕ) (f : PowerSeries L) (k : ℤ) :
    cz (PowerSeries.X ^ w * f) (k + (w : ℤ)) = cz f k := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    rcases lt_or_ge (k + (w : ℤ)) 0 with h' | h'
    · exact cz_neg _ h'
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h'
      rw [hm, cz_nat, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [← Nat.cast_add, cz_nat, cz_nat, PowerSeries.coeff_X_pow_mul]

theorem cz_mul (g f : PowerSeries L) (k : ℤ) (N : ℕ) (hN : k < (N : ℤ)) :
    cz (g * f) k = ∑ i ∈ Finset.range N, PowerSeries.coeff i g * cz f (k - (i : ℤ)) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [cz_neg _ (by omega), mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [cz_nat, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show m + 1 ≤ N by omega))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
      rw [← Nat.cast_sub this, cz_nat]
    · intro i _ hi
      have : m < i := by simpa using hi
      rw [cz_neg _ (by omega), mul_zero]

theorem series_transport {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
    {r r' : ℕ} (w w' : ℕ) (A : Fin r' → PowerSeries L) (Bs : Fin r → PowerSeries L) (κ : L) (hκ : κ ≠ 0)
    (g : PowerSeries L) (c : Fin r' → Fin r → L)
    (hA : ∀ j, (PowerSeries.C κ * PowerSeries.X) ^ w * A j =
      PowerSeries.X ^ w' * (g * ∑ p, PowerSeries.C (c j p) * PowerSeries.rescale κ (Bs p)))
    (h : M →ₗ[L] M') (D : Fin r → M) (D' : Fin r' → M') (hD : ∀ p, h (D p) = ∑ j, c j p • D' j) (k : ℤ) :
    ∑ j, cz (A j) (k + (w' : ℤ)) • D' j = ∑ᶠ i : ℕ, PowerSeries.coeff i g •
      (κ ^ (k - (i : ℤ)) • h (∑ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) • D p)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k + (w : ℤ) < (N : ℤ) := ⟨(k + (w : ℤ)).toNat + 1, by omega⟩
  rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
  · have key : ∀ j, cz (A j) (k + (w' : ℤ)) = ∑ i ∈ Finset.range N, ∑ p, PowerSeries.coeff i g *
        (κ ^ (k - (i : ℤ)) * (cz (Bs p) (k - (i : ℤ) + (w : ℤ)) * c j p)) := by
      intro j
      have h1 := congrArg (fun f => cz f (k + (w : ℤ) + (w' : ℤ))) (hA j)
      rw [cz_X_pow_mul, mul_pow, ← map_pow, mul_assoc, cz_C_mul, add_right_comm, cz_X_pow_mul,
        cz_mul _ _ _ N hN] at h1
      apply mul_left_cancel₀ (pow_ne_zero w hκ)
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cz_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cz_C_mul, cz_rescale, show k + (w : ℤ) - (i : ℤ) = k - (i : ℤ) + (w : ℤ) by ring, zpow_add₀ hκ,
        zpow_natCast]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [key, Finset.sum_smul, map_sum, map_smul, hD, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · intro i hi
    by_contra hc
    apply hi
    have : N ≤ i := by simpa using hc
    have hz : ∀ p, cz (Bs p) (k - (i : ℤ) + (w : ℤ)) = 0 := fun p => cz_neg _ (by omega)
    simp [hz]

end Cz

theorem basis_transport {C S : Type} [CommRing C] [CommRing S] (J : C →+* S) (σ : C →+* C) (σS : S →+* S)
    (hJ : ∀ a, J (σ a) = σS (J a)) {M M' : Type} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    (h : M →+ M') (hh : ∀ (a : S) m, h (a • m) = σS a • h m) (t q : C) (ht : IsUnit (J t)) (hq : IsUnit (J q))
    {r r' : ℕ} (w w' : ℕ) (bn d : Fin r → M) (bn' d' : Fin r' → M') (U : Fin r → Fin r → C)
    (U' : Fin r' → Fin r' → C) (H Cm : Fin r' → Fin r → C)
    (hd : ∀ j, J t ^ w • d j = ∑ i, J (U i j) • bn i) (hd' : ∀ j, J t ^ w' • d' j = ∑ i, J (U' i j) • bn' i)
    (hH : ∀ j, J q • h (bn j) = ∑ i, J (H i j) • bn' i)
    (hU : ∀ k p, t ^ w' * ∑ i, H k i * σ (U i p) = σ t ^ w * q * ∑ j, U' k j * Cm j p) (p : Fin r) :
    h (d p) = ∑ j, J (Cm j p) • d' j := by
  have hu : IsUnit (J t ^ w' * σS (J t) ^ w * J q) := ((ht.pow _).mul ((ht.map σS).pow _)).mul hq
  apply hu.smul_left_cancel.mp
  have e1 : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) =
      ∑ k, J (t ^ w' * ∑ i, H k i * σ (U i p)) • bn' k := by
    have : (J t ^ w' * σS (J t) ^ w * J q) • h (d p) = J t ^ w' • J q • h (J t ^ w • d p) := by
      rw [hh, map_pow, smul_smul, smul_smul]
      congr 1
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, hd, map_sum, Finset.smul_sum, Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hh, smul_comm (J q), hH, Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  have e2 : (J t ^ w' * σS (J t) ^ w * J q) • ∑ j, J (Cm j p) • d' j =
      ∑ k, J (σ t ^ w * q * ∑ j, U' k j * Cm j p) • bn' k := by
    have : ∀ j, (J t ^ w' * σS (J t) ^ w * J q) • J (Cm j p) • d' j =
        (σS (J t) ^ w * J q * J (Cm j p)) • J t ^ w' • d' j := by
      intro j
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [this, hd', Finset.smul_sum, smul_smul, map_mul, map_sum, map_pow, hJ,
      Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [e1, e2]
  simp only [hU]

theorem coord_transport {A : Type} [CommRing A] (σ : A →+* A) {r r' : ℕ} (U V : Matrix (Fin r) (Fin r) A)
    (U' V' : Matrix (Fin r') (Fin r') A) (H Cm : Matrix (Fin r') (Fin r) A) (q q' : A)
    (hq : ∀ a, q * a = 0 → a = 0) (hUV : U * V = 1) (hUV' : U' * V' = 1)
    (hU : H * U.map σ = q • (U' * Cm)) (c : Fin r → A) (c' : Fin r' → A)
    (hc : q • c' = q' • H *ᵥ (σ ∘ c)) : V' *ᵥ c' = q' • Cm *ᵥ (σ ∘ (V *ᵥ c)) := by
  have h1 : V' * H = q • (Cm * V.map σ) := by
    have h2 : U.map σ * V.map σ = 1 := by
      rw [← Matrix.map_mul, hUV, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc V' * H = V' * (H * U.map σ) * V.map σ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = q • (Cm * V.map σ) := by
          rw [hU, Matrix.mul_smul, ← Matrix.mul_assoc, mul_eq_one_comm.mp hUV', Matrix.one_mul, Matrix.smul_mul]
  have h3 : σ ∘ (V *ᵥ c) = V.map σ *ᵥ (σ ∘ c) := by
    funext i
    exact RingHom.map_mulVec σ V c i
  have h4 : q • (V' *ᵥ c') = q • (q' • Cm *ᵥ (σ ∘ (V *ᵥ c))) := by
    rw [← Matrix.mulVec_smul, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h3, Matrix.mulVec_mulVec,
      Matrix.smul_mulVec, smul_comm]
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.smul_apply, smul_eq_mul] at h5 ⊢
  exact sub_eq_zero.mp (hq _ (by rw [mul_sub, h5, sub_self]))

end GlobalTheory.HWL.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNorm
section
noncomputable section

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter Finset GlobalTheory.HWL.Disc

variable {K : Type} [NormedField K] {N : Type} [NormedCommRing N]

def Small (ν : N) : Prop := ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖ν ^ k‖ ≤ C * r ^ k

def Bdd (c : K →+* N) : Prop := ∃ C : ℝ, ∀ x, ‖c x‖ ≤ C * ‖x‖

def ev (c : K →+* N) (ν : N) (a : K⟦X⟧) : N := ∑' k : ℕ, c (coeff k a) * ν ^ k

variable {c : K →+* N} {ν : N}

theorem Bdd.continuous (hc : Bdd c) : Continuous c := by
  obtain ⟨C, h⟩ := hc
  exact AddMonoidHomClass.continuous_of_bound c C h

theorem exists_bound (hc : Bdd c) (hν : Small ν) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ (x : K) (k : ℕ), ‖c x * ν ^ k‖ ≤ C * (‖x‖ * r ^ k) := by
  obtain ⟨C, h⟩ := hc
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine ⟨|C| * |D|, r, by positivity, h0, h1, fun x k => (norm_mul_le _ _).trans ?_⟩
  have e1 : ‖c x‖ ≤ |C| * ‖x‖ := (h x).trans (by gcongr; exact le_abs_self C)
  have e2 : ‖ν ^ k‖ ≤ |D| * r ^ k := (h2 k).trans (by gcongr; exact le_abs_self D)
  calc _ ≤ (|C| * ‖x‖) * (|D| * r ^ k) := by gcongr
    _ = _ := by ring

theorem summable_norm (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Summable fun k : ℕ => ‖c (coeff k a) * ν ^ k‖ := by
  obtain ⟨C, r, -, h0, h1, h⟩ := exists_bound hc hν
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => h _ k) ((ha r h0 h1).mul_left C)

theorem Small.tendsto (hν : Small ν) : Tendsto (fun k : ℕ => ν ^ k) atTop (nhds 0) := by
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine squeeze_zero_norm h2 ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul D

theorem ev_C_mul (hc : Bdd c) (hν : Small ν) [CompleteSpace N] (x : K) {a : K⟦X⟧} (ha : SC a) :
    ev c ν (x • a) = c x * ev c ν a := by
  rw [ev, ev, ← (summable_norm hc hν ha).of_norm.tsum_mul_left]
  simp [mul_assoc]

theorem sum_range_eq (a : K⟦X⟧) (m : ℕ) :
    ∑ k ∈ range m, c (coeff k a) * ν ^ k = Polynomial.eval₂ c ν (trunc m a) := by
  rw [eval₂_trunc_eq_sum_range]

variable [CompleteSpace N]

theorem hasSum_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ν ^ k) (ev c ν a) :=
  (summable_norm hc hν ha).of_norm.hasSum

theorem tendsto_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Tendsto (fun m : ℕ => Polynomial.eval₂ c ν (trunc m a)) atTop (nhds (ev c ν a)) := by
  simpa only [sum_range_eq] using (hasSum_ev hc hν ha).tendsto_sum_nat

theorem ev_add (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a + b) = ev c ν a + ev c ν b := by
  refine HasSum.tsum_eq ?_
  simpa only [map_add (f := _), add_mul] using (hasSum_ev hc hν ha).add (hasSum_ev hc hν hb)

theorem ev_mul (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a * b) = ev c ν a * ev c ν b := by
  rw [ev, ev, ev, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm hc hν ha)
    (summable_norm hc hν hb)]
  refine tsum_congr fun k => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← mem_antidiagonal.1 hp, map_mul, pow_add]
  ring

theorem ev_one : ev c ν 1 = 1 := by
  rw [ev, tsum_eq_single 0 fun k hk => by simp [coeff_one, hk]]
  simp

theorem sc_pow {a : K⟦X⟧} (ha : SC a) (k : ℕ) : SC (a ^ k) := by
  induction k with
  | zero => simpa using sc_coe (1 : Polynomial K)
  | succ k ih => rw [pow_succ]; exact ih.mul ha

theorem ev_pow (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (k : ℕ) :
    ev c ν (a ^ k) = ev c ν a ^ k := by
  induction k with
  | zero => simpa using ev_one
  | succ k ih => rw [pow_succ, pow_succ, ev_mul hc hν (sc_pow ha k) ha, ih]

theorem hasSum_map (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (f : N →+* N) (hf : Continuous f)
    (hfc : ∀ x, f (c x) = c x) : HasSum (fun k : ℕ => c (coeff k a) * f ν ^ k) (f (ev c ν a)) := by
  have := (hasSum_ev hc hν ha).map f hf
  simpa only [Function.comp_def, map_mul, map_pow, hfc] using this

theorem ev_map {O : Type} [CommRing O] (j : O →+* K) (hν : Small ν) (hc : Bdd c) (f : O⟦X⟧ →+* N)
    (hC : ∀ o, f (C o) = c (j o)) (hX : f X = ν) (hf : ∀ a, ‖f a‖ ≤ 1) (a : O⟦X⟧) (ha : SC (map j a)) :
    ev c ν (map j a) = f a := by
  refine tendsto_nhds_unique (hasSum_ev hc hν ha).tendsto_sum_nat ?_
  have key : ∀ m : ℕ, ∑ k ∈ range m, c (coeff k (map j a)) * ν ^ k =
      f a - ν ^ m * f (mk fun i => coeff (i + m) a) := by
    intro m
    have e0 := congrArg f (eq_X_pow_mul_shift_add_trunc m a)
    rw [e0, map_add (f := _), map_mul, map_pow, hX, add_sub_cancel_left, trunc_apply, Polynomial.coe_def]
    have e : (mk (∑ k ∈ Ico 0 m, Polynomial.monomial k (coeff k a)).coeff : O⟦X⟧) =
        ∑ k ∈ range m, C (coeff k a) * X ^ k := by
      ext n
      simp [coeff_X_pow, Polynomial.coeff_monomial, Polynomial.finsetSum_coeff, Finsupp.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    simp only [map_mul, map_pow, hX, hC, coeff_map]
  simp only [key]
  conv => rhs; rw [← sub_zero (f a)]
  refine tendsto_const_nhds.sub (squeeze_zero_norm (a := fun m => ‖ν ^ m‖) (fun m => ?_) ?_)
  · exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hf _))
  · simpa using hν.tendsto.norm

theorem hasSum_subst [IsUltrametricDist K] (hc : Bdd c) (hν : Small ν) {y a : K⟦X⟧} (hy0 : constantCoeff y = 0)
    (hy : ∀ k, ‖coeff k y‖ ≤ 1) (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ev c ν y ^ k) (ev c ν (subst y a)) := by
  obtain ⟨C, r, hC, h0, h1, h⟩ := exists_bound hc hν
  have hy' : SC y := sc_of_le 0 fun k => by simpa using hy k
  have hp : ∀ k n, ‖coeff n (y ^ k)‖ ≤ 1 := fun k n => by
    simpa using norm_coeff_pow_le y n (r := 1) (R := 1) zero_le_one zero_le_one (fun i _ => by simpa using hy i) k n le_rfl
  have hz : ∀ k n, n < k → coeff n (y ^ k) = 0 := fun k n hn =>
    X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hy0) k) n hn
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ r = ρ * ρ :=
    ⟨√r, Real.sqrt_pos.2 h0, by rwa [Real.sqrt_lt' one_pos, one_pow], (Real.mul_self_sqrt h0.le).symm⟩
  let F : ℕ × ℕ → N := fun p => c (coeff p.1 a * coeff p.2 (y ^ p.1)) * ν ^ p.2
  have hF : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (C * (‖coeff p.1 a‖ * ρ ^ p.1)) * ρ ^ p.2)
      (Summable.mul_of_nonneg ((ha ρ hρ0 hρ1).mul_left C) (summable_geometric_of_lt_one hρ0.le hρ1)
        (fun _ => by positivity) fun _ => by positivity) fun p => ?_
    by_cases hlt : p.2 < p.1
    · simp only [F, hz _ _ hlt, mul_zero, map_zero, zero_mul, norm_zero]
      positivity
    · refine (h _ _).trans ?_
      have e : ρ ^ p.2 ≤ ρ ^ p.1 := pow_le_pow_of_le_one hρ0.le hρ1.le (not_lt.1 hlt)
      rw [norm_mul, hρ, mul_pow]
      calc _ ≤ C * (‖coeff p.1 a‖ * 1 * (ρ ^ p.1 * ρ ^ p.2)) := by gcongr; exact hp _ _
        _ = _ := by ring
  have h2 : HasSum (fun n : ℕ => c (coeff n (subst y a)) * ν ^ n) (∑' p, F p) := by
    refine HasSum.prod_fiberwise ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hF.hasSum) fun n => ?_
    have e : coeff n (subst y a) = ∑ k ∈ range (n + 1), coeff k a * coeff n (y ^ k) := by
      rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hy0), finsum_eq_sum_of_support_subset (s := range (n + 1))]
      · simp
      · intro k hk
        by_contra hk'
        apply hk
        simp only [coe_range, Set.mem_Iio, not_lt] at hk'
        simp [hz k n hk']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, sum_mul]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    simp [F, hz k n hk]
  rw [show ev c ν (subst y a) = _ from h2.tsum_eq]
  refine HasSum.prod_fiberwise hF.hasSum fun k => ?_
  rw [← ev_pow hc hν hy']
  simpa only [F, map_mul, mul_assoc] using (hasSum_ev hc hν (sc_pow hy' k)).mul_left (c (coeff k a))

end GlobalTheory.HWL.BanachEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLocalOddResidueOfLieAlgebra
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

section Assembly

variable {K K' : UQ}

def prodEquiv (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    ((overExt φ B₁ ((RingHom.fst B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.fst (hψ e))
        (fun e => congrArg Prod.fst (hσ e))).prod
      (overExt φ B₂ ((RingHom.snd B₁.A B₂.A).comp ψ) (fun e => congrArg Prod.snd (hψ e))
        (fun e => congrArg Prod.snd (hσ e)))).A ≃ₐ[K'.E] (overExt φ (B₁.prod B₂) ψ hψ hσ).A :=
  { RingEquiv.refl (B₁.A × B₂.A) with commutes' := fun _ => rfl }

theorem prodEquiv_isIso (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩

theorem prod_unitary (B₁ B₂ : InvAlg K) (hu₁ : B₁.g * B₁.σ B₁.g = 1) (hu₂ : B₂.g * B₂.σ B₂.g = 1) :
    (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 :=
  Prod.ext hu₁ hu₂

theorem prod_integral (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl

end Assembly

theorem unitLemma_local_of_lie : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := _root_.GlobalTheory.UnitLemma.ResDeg.card_residueField_prod K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := _root_.GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := _root_.GlobalTheory.UnitLemma.Unr.exists_unr_embedding K hK (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := _root_.GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact _root_.GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := _root_.GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent hL K' (hodd hK) C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => _root_.GlobalTheory.UnitLemma.Unr.N_overExt K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact _root_.GlobalTheory.UnitLemma.Unr.N_overExt K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := _root_.GlobalTheory.UnitLemma.Unr.eta_overExt K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := _root_.GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]

end GlobalTheory.UnitLemma.Unr
end
end

