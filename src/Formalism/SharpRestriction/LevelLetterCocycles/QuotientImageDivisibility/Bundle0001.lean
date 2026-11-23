module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.DvdOfDvdImage
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Wd

open PowerSeries

variable {O LL : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
  (hinj : Function.Injective (algebraMap O LL)) (l : O)
  (ψ : PowerSeries O →+* PowerSeries LL) (hψC : ∀ o : O, ψ (PowerSeries.C o) = PowerSeries.C (algebraMap O LL o))
  (u : PowerSeries LL) (hu : IsUnit u) (hψ : ψ (PowerSeries.X + PowerSeries.C l) = PowerSeries.X * u)
include hinj hψC hu hψ


theorem poly_eq_zero : ∀ (k : ℕ) (r : Polynomial O), r.degree < k →
    PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) → r = 0 := by
  have dvd_of_dvd_isUnit_mul_lemma {R : Type _} [CommRing R] {u f g : R} (hu : IsUnit u)
      (h : g ∣ u * f) : g ∣ f := by
    obtain ⟨v, rfl⟩ := hu
    have e : f = ↑v⁻¹ * (↑v * f) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h _
  have hψX : ψ PowerSeries.X = PowerSeries.X * u - PowerSeries.C (algebraMap O LL l) := by
    have h := hψ
    rw [map_add (f := _), hψC] at h
    exact eq_sub_of_add_eq h
  intro k
  induction k with
  | zero =>
    intro r hr _
    by_contra hr0
    rw [Polynomial.degree_eq_natDegree hr0] at hr
    have h0 : r.natDegree < 0 := by exact_mod_cast hr
    omega
  | succ k ih =>
    intro r hr hdvd
    have hmon : (Polynomial.X + Polynomial.C l : Polynomial O).Monic := Polynomial.monic_X_add_C l
    have hrem : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) = Polynomial.C (r.eval (-l)) := by
      have hg : (Polynomial.X + Polynomial.C l : Polynomial O) = Polynomial.X - Polynomial.C (-l) := by
        rw [map_neg, sub_neg_eq_add]
      rw [hg]
      exact Polynomial.modByMonic_X_sub_C_eq_C_eval r (-l)
    have hsplit : r = Polynomial.C (r.eval (-l)) +
        (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) := by
      have h1 : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) +
          (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = r := by
        first
          | exact Polynomial.modByMonic_add_div r (Polynomial.X + Polynomial.C l)
          | exact Polynomial.modByMonic_add_div r _ hmon
          | exact Polynomial.modByMonic_add_div r hmon
      rw [hrem] at h1
      exact h1.symm
    have hqdeg : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < k := by
      by_cases hq0 : Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = 0
      · rw [hq0, Polynomial.degree_zero]
        first
          | exact WithBot.bot_lt_coe _
          | simp
      · have hr0 : r ≠ 0 := by
          rintro rfl
          exact hq0 (Polynomial.zero_divByMonic _)
        have hpos : 0 < (Polynomial.X + Polynomial.C l : Polynomial O).degree := by
          first
            | (rw [Polynomial.degree_X_add_C]; exact zero_lt_one)
            | simp
        have h1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < r.degree := by
          first
            | exact Polynomial.degree_divByMonic_lt r (Polynomial.X + Polynomial.C l) hr0 hpos
            | exact Polynomial.degree_divByMonic_lt r _ hmon hr0 hpos
            | exact Polynomial.degree_divByMonic_lt r hmon hr0 hpos
        rw [Polynomial.degree_eq_natDegree hq0, Polynomial.degree_eq_natDegree hr0] at h1
        rw [Polynomial.degree_eq_natDegree hr0] at hr
        rw [Polynomial.degree_eq_natDegree hq0]
        have a1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < r.natDegree := by
          exact_mod_cast h1
        have a2 : r.natDegree < k + 1 := by exact_mod_cast hr
        have a3 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < k := by omega
        exact_mod_cast a3
    obtain ⟨c, q, hrq, hq⟩ : ∃ (c : O) (q : Polynomial O),
        r = Polynomial.C c + (Polynomial.X + Polynomial.C l) * q ∧ q.degree < k :=
      ⟨_, _, hsplit, hqdeg⟩
    have hψr : ψ (r : PowerSeries O) =
        PowerSeries.C (algebraMap O LL c) + PowerSeries.X * (u * ψ (q : PowerSeries O)) := by
      rw [hrq]
      first
        | (simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
            map_add, map_mul, hψC, hψX]; ring)
        | (simp [hψC, hψX]; ring)
    have hX : PowerSeries.X ∣ ψ (r : PowerSeries O) :=
      (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hdvd
    rw [hψr, PowerSeries.X_dvd_iff] at hX
    first
      | simp only [map_add (f := _), map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
          zero_mul, add_zero] at hX
      | simp at hX
    have hc0 : c = 0 := hinj (hX.trans (map_zero _).symm)
    simp only [hc0, map_zero, zero_add] at hψr
    rw [hψr, pow_succ'] at hdvd
    have h2 : PowerSeries.X ^ k ∣ u * ψ (q : PowerSeries O) :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hdvd
    have hq0 : q = 0 := ih q hq (dvd_of_dvd_isUnit_mul_lemma hu h2)
    rw [hrq, hc0, hq0]
    simp

theorem dvd_of_dvd_image [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : l ∈ IsLocalRing.maximalIdeal O) (k : ℕ) (a : PowerSeries O)
    (ha : PowerSeries.X ^ k ∣ ψ a) : (PowerSeries.X + PowerSeries.C l) ^ k ∣ a := by
  have hres : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) =
      PowerSeries.X ^ k := by
    rw [map_pow, map_add (f := _), PowerSeries.map_X, PowerSeries.map_C,
      (IsLocalRing.residue_eq_zero_iff l).mpr hlm, map_zero, add_zero]
  have hg : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) ≠ 0 := by
    rw [hres]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hg
  have hdeg : r.degree < k := by
    have h := hdiv.degree_lt
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) l = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hlm
    first
      | simpa [hz, PowerSeries.order_X_pow] using h
      | simpa [hz] using h
      | (rw [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | (simp only [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | simpa [hres] using h
  have hψa : ψ a = (PowerSeries.X * u) ^ k * ψ q + ψ (r : PowerSeries O) := by
    rw [hdiv.eq_mul_add, map_add (f := _), map_mul, map_pow, hψ]
  have h1 : PowerSeries.X ^ k ∣ (PowerSeries.X * u) ^ k * ψ q :=
    dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  have h2 : PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) := by
    rw [hψa] at ha
    first
      | exact (dvd_add_right h1).mp ha
      | simpa using dvd_sub ha h1
  have hr0 : r = 0 := poly_eq_zero hinj l ψ hψC u hu hψ k r hdeg h2
  rw [hdiv.eq_mul_add, hr0, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

end Formalism.MainNotions.N.Pv.LocalLengthBound.Wd
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def LB (m : ℤ) (f : ℤ → V) : Prop := ∀ k < m, f k = 0

def smulS (g : PowerSeries LL) (f : ℤ → V) : ℤ → V :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem smulS_eq_sum {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : smulS g f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (k - j) := by
  show ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j) = _
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hjN
  apply hj
  rw [hf (k - j) (by omega), smul_zero]

theorem LB_mono {m m' : ℤ} {f : ℤ → V} (hf : LB m f) (h : m' ≤ m) : LB m' f := by
  intro k hk
  exact hf k (lt_of_lt_of_le hk h)

theorem LB_smulS {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) : LB m (smulS g f) := by
  intro k hk
  rw [smulS_eq_sum hf g k 0 (by omega)]
  simp

theorem LB_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f + f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f - f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) : LB m (c • f) := by
  intro k hk
  simp [hf k hk]

private theorem exists_nat_gt_int_sub (k m : ℤ) : ∃ N : ℕ, k - m < N := by
  first
  | exact exists_nat_gt (k - m)
  | exact ⟨(k - m).toNat + 1, by omega⟩
  | exact ⟨(k - m).toNat + 1, by have := Int.self_le_toNat (k - m); omega⟩

theorem smulS_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f + f') = smulS g f + smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.add_apply, smulS_eq_sum (LB_add hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, smul_add]

theorem smulS_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f - f') = smulS g f - smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.sub_apply, smulS_eq_sum (LB_sub hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, smul_sub]

theorem smulS_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (c : LL) :
    smulS g (c • f) = c • smulS g f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.smul_apply, smulS_eq_sum (LB_smul hf c) g k N hN,
    smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

private theorem smulS_C_eq_smul_of_LB {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf _ k (N + 1) (by omega), Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [PowerSeries.coeff_C, hj]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h0

theorem smulS_one {m : ℤ} {f : ℤ → V} (hf : LB m f) : smulS (1 : PowerSeries LL) f = f := by
  first
  | simpa using smulS_C_eq_smul_of_LB hf (1 : LL)
  | (have h1 := smulS_C_eq_smul_of_LB hf (1 : LL); rwa [map_one, one_smul] at h1)

theorem smulS_C {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  exact smulS_C_eq_smul_of_LB hf c

theorem smulS_X_pow {m : ℤ} {f : ℤ → V} (hf : LB m f) (K : ℕ) :
    smulS ((PowerSeries.X : PowerSeries LL) ^ K) f = fun k => f (k - K) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf _ k (N + K + 1) (by omega), Finset.sum_eq_single K]
  · simp [PowerSeries.coeff_X_pow]
  · intro j _ hj
    simp [PowerSeries.coeff_X_pow, hj]
  · intro hK
    exact absurd (Finset.mem_range.mpr (by omega)) hK

theorem smulS_mul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g h : PowerSeries LL) :
    smulS (g * h) f = smulS g (smulS h f) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  have hR : ∀ i : ℕ, smulS h f (k - i) =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j h • f (k - i - j) :=
    fun i => smulS_eq_sum hf h (k - i) N (by omega)
  have hzero : ∀ i j : ℕ, N ≤ i + j → f (k - i - j) = 0 := fun i j hij => hf _ (by omega)
  calc smulS (g * h) f k
      = ∑ n ∈ Finset.range N, PowerSeries.coeff n (g * h) • f (k - n) :=
        smulS_eq_sum hf _ k N hN
    _ = ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i g * PowerSeries.coeff (n - i) h) • f (k - i - (n - i : ℕ)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [PowerSeries.coeff_mul, Finset.sum_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := by
          simp only [Finset.mem_range, Nat.succ_eq_add_one] at hi
          omega
        have e : k - (n : ℤ) = k - i - ((n - i : ℕ) : ℤ) := by omega
        rw [e]
        try rfl
    _ = ∑ i ∈ Finset.range N, ∑ n ∈ Finset.Ico i N,
          (PowerSeries.coeff i g * PowerSeries.coeff (n - i) h) • f (k - i - (n - i : ℕ)) :=
        Finset.sum_comm' fun n i => by
          simp only [Finset.mem_range, Finset.mem_Ico]
          constructor <;> intro hh <;> omega
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i),
          (PowerSeries.coeff i g * PowerSeries.coeff j h) • f (k - i - j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Nat.add_sub_cancel_left]
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (PowerSeries.coeff i g * PowerSeries.coeff j h) • f (k - i - j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        apply Finset.sum_subset
        · intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
        · intro j hj hj'
          simp only [Finset.mem_range, not_lt] at hj hj'
          simp only [hzero i j (by omega), smul_zero]
    _ = smulS g (smulS h f) k := by
        rw [smulS_eq_sum (LB_smulS hf h) g k N hN]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hR, Finset.smul_sum, smul_smul]

theorem smulS_inv {m : ℤ} {f : ℤ → V} (hf : LB m f) (u : PowerSeries LL)
    (hu : PowerSeries.constantCoeff u ≠ 0) : smulS u⁻¹ (smulS u f) = f := by
  have h1 : u⁻¹ * u = 1 := by
    first
    | exact PowerSeries.inv_mul_cancel u hu
    | exact PowerSeries.inv_mul_cancel hu
    | exact PowerSeries.inv_mul_cancel _ hu
    | (rw [mul_comm]; exact PowerSeries.mul_inv_cancel u hu)
  rw [← smulS_mul hf, h1, smulS_one hf]

def Dg (Fil : ℤ → Submodule LL V) (s : ℤ) (f : ℤ → V) : Prop := ∀ k, f k ∈ Fil (s - k)

theorem Dg_smulS {Fil : ℤ → Submodule LL V} (hF : Antitone Fil) {m s : ℤ} {f : ℤ → V}
    (hf : LB m f) (hD : Dg Fil s f) (g : PowerSeries LL) : Dg Fil s (smulS g f) := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf g k N hN]
  refine sum_mem fun j _ => Submodule.smul_mem _ _ ?_
  exact hF (by omega : s - k ≤ s - (k - (j : ℤ))) (hD (k - j))

def resc (χ : LL) (f : ℤ → V) : ℤ → V := fun k => (χ ^ k) • f k

theorem LB_resc {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) : LB m (resc χ f) := by
  intro k hk
  show (χ ^ k) • f k = 0
  rw [hf k hk, smul_zero]

theorem smulS_rescale {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) (hχ : χ ≠ 0)
    (g : PowerSeries LL) : smulS (PowerSeries.rescale χ g) (resc χ f) = resc χ (smulS g f) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum (LB_resc hf χ) _ k N hN]
  show _ = χ ^ k • smulS g f k
  rw [smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : χ ^ j * χ ^ (k - (j : ℤ)) = χ ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hχ]
    congr 1
    omega
  show PowerSeries.coeff j (PowerSeries.rescale χ g) • (χ ^ (k - (j : ℤ)) • f (k - j)) =
    χ ^ k • (PowerSeries.coeff j g • f (k - j))
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul, mul_right_comm, e]

end Formalism.MainNotions.N.Pv.LocalLengthBound.Ser
end
end

