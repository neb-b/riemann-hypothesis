module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ExpStep
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK
open Polynomial

private theorem exp_cong (w : ℕ) (g : ℤ[X]) : (X ^ w - 1 : ℤ[X]) ∣ expand ℤ (1 + w) g - g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | monomial n a =>
    rw [expand_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← mul_sub]
    apply dvd_mul_of_dvd_right
    have h1 : (X : ℤ[X]) ^ (n * (1 + w)) - X ^ n = X ^ n * ((X ^ w) ^ n - 1 ^ n) := by
      ring
    rw [h1]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ _) _

private theorem exp_step (w j : ℕ) (x : ℤ[X]) (hx : (X ^ w - 1 : ℤ[X]) ^ j ∣ x) :
    (X ^ w - 1 : ℤ[X]) ^ (j + 1) ∣ expand ℤ (1 + w) x - ((1 + w : ℕ) : ℤ[X]) ^ j * x := by
  obtain ⟨y, rfl⟩ := hx
  have hE : expand ℤ (1 + w) (X ^ w - 1 : ℤ[X]) = (X ^ w - 1) * ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i := by
    rw [mul_comm, geom_sum_mul]
    simp only [map_sub, map_pow, expand_X, map_one, ← pow_mul, mul_comm]
  have hSk : (X ^ w - 1 : ℤ[X]) ∣ ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i - ((1 + w : ℕ) : ℤ[X]) := by
    have h1 : ((1 + w : ℕ) : ℤ[X]) = ∑ i ∈ Finset.range (1 + w), ((1 : ℤ[X]) ^ i) := by simp
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow ((X : ℤ[X]) ^ w) 1 i
  have hSj := hSk.trans (sub_dvd_pow_sub_pow _ _ j)
  have key : expand ℤ (1 + w) ((X ^ w - 1 : ℤ[X]) ^ j * y) - ((1 + w : ℕ) : ℤ[X]) ^ j * ((X ^ w - 1) ^ j * y) =
      (X ^ w - 1) ^ j * ((( ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i) ^ j - ((1 + w : ℕ) : ℤ[X]) ^ j) *
        expand ℤ (1 + w) y + ((1 + w : ℕ) : ℤ[X]) ^ j * (expand ℤ (1 + w) y - y)) := by
    rw [map_mul, map_pow, hE, mul_pow]; ring
  rw [key, pow_succ]
  exact mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left hSj _) (dvd_mul_of_dvd_right (exp_cong w y) _))

private theorem exp_pow (k i : ℕ) : (((expand ℤ k).toLinearMap : Module.End ℤ ℤ[X]) ^ i) X = X ^ k ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; simp [← pow_mul, pow_succ']

private theorem exp_dvd (w M : ℕ) : (X ^ w - 1 : ℤ[X]) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
    (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i := by
  have hdeg : (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).natDegree = M := by
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hsum : ∑ i ∈ Finset.range (M + 1),
      (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i =
      (aeval ((expand ℤ (1 + w)).toLinearMap : Module.End ℤ ℤ[X])
        (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X])) X := by
    rw [aeval_eq_sum_range, hdeg, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, exp_pow]
  rw [hsum]
  clear hsum hdeg
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ_comm, map_mul, Module.End.mul_apply]
    have h := exp_step w n _ ih
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      AlgHom.toLinearMap_apply]
    convert h using 3
    rw [zsmul_eq_mul]; push_cast; ring

private theorem nat_dvd (l c ν n : ℕ) (hl : l.Prime) (h0 : n ≠ 0) (hn : n < l ^ c) :
    (n : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ c := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  have hac : a ≤ c := by
    by_contra hca
    have h1 : l ^ c ≤ l ^ a := Nat.pow_le_pow_right hl.pos (by omega)
    have h2 : l ^ a ≤ l ^ a * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero l)))
    omega
  have hcop : Nat.Coprime u (l ^ ν) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hu))
  refine ⟨(l : ZMod (l ^ ν)) ^ (c - a) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)), ?_⟩
  have hv : (u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1 :=
    (ZMod.unitOfCoprime u hcop).mul_inv
  calc (l : ZMod (l ^ ν)) ^ c = (l : ZMod (l ^ ν)) ^ a * (l : ZMod (l ^ ν)) ^ (c - a) *
        ((u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν))) := by
        rw [hv, mul_one, ← pow_add, Nat.add_sub_cancel' hac]
    _ = _ := by push_cast; ring

private theorem diff_dvd (l c ν s t : ℕ) (hl : l.Prime) (h : s ≠ t) (hs : s < l ^ c) (ht : t < l ^ c) :
    ((s : ZMod (l ^ ν)) - t) ∣ (l : ZMod (l ^ ν)) ^ c := by
  rcases lt_or_gt_of_ne h with hst | hst
  · have h1 := nat_dvd l c ν (t - s) hl (by omega) (by omega)
    rw [Nat.cast_sub hst.le] at h1
    rw [← neg_sub, neg_dvd]
    exact h1
  · have h1 := nat_dvd l c ν (s - t) hl (by omega) (by omega)
    rwa [Nat.cast_sub hst.le] at h1

private theorem sgl_dvd {q : ℕ} [NeZero q] (a b : ZMod q) (h : a ∣ b) :
    (AddMonoidAlgebra.single a 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ∣ AddMonoidAlgebra.single b 1 - 1 := by
  obtain ⟨c, rfl⟩ := h
  have hc : a * c = c.val • a := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  rw [hc]
  have h1 := sub_dvd_pow_sub_pow (AddMonoidAlgebra.single a (1 : ℤ)) 1 c.val
  rwa [one_pow, AddMonoidAlgebra.single_pow, one_pow] at h1

private theorem alg_dvd (q w M : ℕ) :
    (AddMonoidAlgebra.single (w : ZMod q) 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
      AddMonoidAlgebra.single ((1 + (w : ZMod q)) ^ i)
        ((∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i) := by
  have h := map_dvd (aeval (R := ℤ) (AddMonoidAlgebra.single (1 : ZMod q) (1 : ℤ))) (exp_dvd w M)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, map_pow, map_sub, map_one, aeval_X, AddMonoidAlgebra.single_pow, one_pow,
    nsmul_one, AddMonoidAlgebra.smul_single', mul_one, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h
  simpa only [map_pow] using h

private def push (q : ℕ) (t : ZMod q) : ZMod q × ZMod q →+ ZMod q where
  toFun x := x.1 + t * x.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring

theorem UpperTheory.V.ZK.sEta :
    UpperTheory.V.ZK.SEta := by
  intro l c ν M hl hM _ t₀
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hF := alg_dvd (l ^ ν) (l ^ c) M
  simp only [Nat.cast_pow] at hF
  let φ : ZMod (l ^ ν) → AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν)) :=
    fun t => AddMonoidAlgebra.mapDomainRingHom ℤ (push (l ^ ν) t)
  have hφ : ∀ (t : ZMod (l ^ ν)) (η : AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν))),
      φ t η = AddMonoidAlgebra.mapDomain (fun x : ZMod (l ^ ν) × ZMod (l ^ ν) => x.1 + t * x.2) η := by
    intro t η
    simp only [φ, AddMonoidAlgebra.mapDomainRingHom_apply]
    rfl
  have hφs : ∀ (t : ZMod (l ^ ν)) (x : ZMod (l ^ ν) × ZMod (l ^ ν)),
      φ t (AddMonoidAlgebra.single x 1) = AddMonoidAlgebra.single (x.1 + t * x.2) 1 := by
    intro t x; rw [hφ, AddMonoidAlgebra.mapDomain_single]
  let ι : AddMonoidAlgebra ℤ (ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) :=
    AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inl (ZMod (l ^ ν)) (ZMod (l ^ ν)))
  have hφι : ∀ t y, φ t (ι y) = y := by
    intro t y
    refine AddMonoidAlgebra.induction_linear y (by simp) (fun a b ha hb => by rw [map_add (f := _), map_add (f := _), ha, hb])
      (fun m r => ?_)
    simp only [ι, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, hφ]
    simp
  set s : Finset (Fin (M + 1)) := Finset.univ.erase t₀ with hs
  have hdiv : ∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1) ∣
      (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) ^ M := by
    have hcard : s.card = M := by simp [hs, Finset.card_erase_of_mem]
    calc _ ∣ ∏ _t' ∈ s, (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) :=
          Finset.prod_dvd_prod_of_dvd _ _ fun t' ht' => sgl_dvd _ _ (diff_dvd l c ν t₀ t' hp
            (fun h => (Finset.ne_of_mem_erase ht') (Fin.ext h).symm)
            (by have := t₀.isLt; omega) (by have := t'.isLt; omega))
      _ = _ := by rw [Finset.prod_const, hcard]
  obtain ⟨Q, hQ⟩ := hdiv.trans hF
  refine ⟨((∏ t' ∈ s, (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
      AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
      ι (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q)).coeff, ?_, ?_⟩
  · intro t ht
    rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod]
    rw [Finset.prod_eq_zero (i := t) (by simp [hs, ht]) (by rw [map_sub, hφs, hφs]; simp), zero_mul,
      AddMonoidAlgebra.coeff_zero]
  · rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod, hφι]
    have hfac : ∀ t' : Fin (M + 1), φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1) =
        AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ) *
          (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) 1 - 1) := by
      intro t'
      rw [map_sub, hφs, hφs, mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def,
        mul_one]
      simp
    have h1 : (∏ t' ∈ s, AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ)) *
        AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 = 1 := by
      rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, add_neg_cancel,
        Finset.prod_const_one, mul_one, AddMonoidAlgebra.one_def]
    have hmain : (∏ t' ∈ s, φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
        (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q) =
        (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
          ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q := by
      simp only [hfac, Finset.prod_mul_distrib]
      linear_combination (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
        ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q * h1
    rw [hmain, ← hQ]
    simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ExponentLe
section
namespace UpperTheory.V.ZK.TorsionExponentBound

theorem exponent_le (e n N m D : ℝ) (he : 1 ≤ e) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 4 * e + 6)
    (hm : m ≤ 2 * e + 1) (hD : 1 ≤ D) :
    12 * (m + 1) * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + (m + 1) * (2 * (n * N * N)) + 2 * m ≤
      (2 * e * n) ^ 24 * Real.log (2 * D) := by
  have hD2 : (0 : ℝ) < 2 * D := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log (2 * D) := Real.log_le_log (by norm_num) (by linarith)
  have hL : (0.69 : ℝ) < Real.log (2 * D) := by linarith
  have ha1 : 1 ≤ e * n := by nlinarith
  have hea : e ≤ e * n := by nlinarith
  have hP1 : 1 ≤ n * N := by nlinarith
  have hP : n * N ≤ 10 * (e * n) := by nlinarith
  have hNa : N ≤ 10 * (e * n) := by linarith
  have hm1 : m + 1 ≤ 4 * (e * n) := by linarith
  have hlogP : Real.log (2 * D * (n * N)) ≤ 16 * (e * n) * Real.log (2 * D) := by
    rw [Real.log_mul (ne_of_gt hD2) (ne_of_gt (by linarith))]
    have := Real.log_le_sub_one_of_pos (show 0 < n * N by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hL.le) (by linarith : (0 : ℝ) ≤ 16 * (e * n) - 1)]
  have hlogP0 : 0 ≤ Real.log (2 * D * (n * N)) := Real.log_nonneg (by nlinarith)
  have hA0 : 0 ≤ 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) := by
    have : 0 ≤ n * N := by linarith
    positivity
  have hA : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) ≤
      1920300 * (e * n) ^ 5 * Real.log (2 * D) := by
    have h3 : (n * N) ^ 3 ≤ (10 * (e * n)) ^ 3 := pow_le_pow_left₀ (by linarith) hP 3
    have t1 : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) ≤
        12 * (10 * (e * n)) ^ 3 * (10 * (e * n)) * (16 * (e * n) * Real.log (2 * D)) := by
      have : 0 ≤ (n * N) ^ 3 := by positivity
      have : 0 ≤ N := by linarith
      gcongr
    have t2 : 2 * (n * N * N) ≤ 300 * (e * n) ^ 5 * Real.log (2 * D) := by
      have q1 : n * N * N ≤ 10 * (e * n) * (10 * (e * n)) := by
        apply mul_le_mul hP hNa (by linarith) (by linarith)
      have q2 : (e * n) ^ 2 ≤ (e * n) ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
      have q3 : 0 ≤ (e * n) ^ 5 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL.le q3]
    have q4 : 0 ≤ Real.log (2 * D) := by linarith
    nlinarith [t1, t2]
  have hE : (2 * e * n) ^ 24 = 2 ^ 24 * (e * n) ^ 24 := by ring
  have hp6 : (e * n) ^ 6 ≤ (e * n) ^ 24 := pow_le_pow_right₀ ha1 (by norm_num)
  have hp1 : e * n ≤ (e * n) ^ 6 := by
    calc e * n = (e * n) ^ 1 := (pow_one _).symm
      _ ≤ (e * n) ^ 6 := pow_le_pow_right₀ ha1 (by norm_num)
  have hLpos : 0 ≤ Real.log (2 * D) := by linarith
  have k1 : (m + 1) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) ≤
      4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) := by
    calc _ ≤ 4 * (e * n) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) :=
          mul_le_mul_of_nonneg_right hm1 hA0
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by linarith)
  have k2 : 2 * m ≤ 12 * (e * n) ^ 6 * Real.log (2 * D) := by
    nlinarith [mul_le_mul_of_nonneg_right hp1 hLpos]
  have k3 : (e * n) ^ 6 * Real.log (2 * D) ≤ (e * n) ^ 24 * Real.log (2 * D) :=
    mul_le_mul_of_nonneg_right hp6 hLpos
  rw [hE]
  have k4 : 4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) =
      7681200 * ((e * n) ^ 6 * Real.log (2 * D)) := by ring
  nlinarith [k1, k2, k3, k4]

end UpperTheory.V.ZK.TorsionExponentBound

open NumberField UpperTheory.V

namespace UpperTheory.V.ZK

theorem torsAll : ∃ C : ℝ, ∀ (L) [Field L] [NumberField L], IsTotallyComplex L →
    ∀ e N m : ℕ, 1 ≤ e → 1 ≤ N → N ≤ 4 * e + 6 → m ≤ 2 * e + 1 →
      Finite (UpperTheory.V.K.torsHGL L N m) ∧
        Real.log (Nat.card (UpperTheory.V.K.torsHGL L N m)) ≤
          UpperTheory.V.kBound C e (Module.finrank ℚ L) (discr L).natAbs := by
  refine ⟨24, ?_⟩
  intro L _ _ hL e N m he hN1 hN hm
  haveI := hL
  have ht := UpperTheory.V.KT.tors_le L N m
  refine ⟨ht.1, ?_⟩
  have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
  have hD : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero L)
  have hdd : 1 ≤ Module.finrank ℚ L * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hA := UpperTheory.V.KT.orbnum L N m hN1
  have hBn : 0 < 2 * (discr L).natAbs * (Module.finrank ℚ L * N) := by positivity
  have hB : (0 : ℝ) < ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) := by exact_mod_cast hBn
  have hAexp : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
      Real.exp (12 * ((m : ℝ) + 1) * ((Module.finrank ℚ L : ℝ) * N) ^ 3 * N *
        Real.log (2 * ((discr L).natAbs : ℝ) * ((Module.finrank ℚ L : ℝ) * N))) := by
    have h1 : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
        ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) ^
          (12 * (m + 1) * (Module.finrank ℚ L * N) ^ 3 * N) := by exact_mod_cast hA
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hsexp : (((3 ^ (UpperTheory.V.KT.dd L N * N) : ℕ)) : ℝ) ≤
      Real.exp (2 * ((Module.finrank ℚ L : ℝ) * N * N)) := by
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ (Module.finrank ℚ L : ℝ) * N * N := by positivity
    nlinarith
  have hs1 : 1 ≤ 3 ^ (UpperTheory.V.KT.dd L N * N) := Nat.one_le_pow _ _ (by norm_num)
  have key := ht.log_le_exp hs1 hAexp hsexp
  refine key.trans ?_
  unfold UpperTheory.V.kBound
  apply Real.exp_le_exp.2
  have hE := UpperTheory.V.ZK.TorsionExponentBound.exponent_le (e : ℝ) (Module.finrank ℚ L : ℝ) (N : ℝ) (m : ℝ)
    ((discr L).natAbs : ℝ) (by exact_mod_cast he) (by exact_mod_cast hn) (by exact_mod_cast hN1)
    (by exact_mod_cast hN) (by exact_mod_cast hm) (by exact_mod_cast hD)
  refine hE.trans (le_of_eq ?_)
  rw [show ((24 : ℝ)) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end UpperTheory.V.ZK

open NumberField UpperTheory.V in
theorem UpperTheory.V.ZK.sTors :
    UpperTheory.V.ZK.STors := by
  obtain ⟨C, h⟩ := UpperTheory.V.ZK.torsAll
  exact ⟨C, fun L _ _ hL E hE m hm => (h L hL E (4 * E + 6) m hE (by omega) le_rfl hm).2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.FProd
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

noncomputable section

namespace UpperTheory.V.ZK.Coc

variable {A K : Type} [CommRing A] [CommGroup K]

private def F (u : K → K → A) (v : K → A) : (n : ℕ) → (Fin n → K) → A
  | 0, _ => 1
  | 1, g => v (g 0)
  | n + 2, g => u (g 0) (g 1) * F u v n fun i => g i.succ.succ

private theorem F_coc (u : K → K → A) (v : K → A) (hu : ∀ a b c, u b c - u (a * b) c + u a (b * c) - u a b = 0)
    (hv : ∀ a b, v (a * b) = v a + v b) : ∀ (n : ℕ) (g : Fin (n + 1) → K),
    F u v n (fun i => g i.succ) + ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) * F u v n (Fin.contractNth j (· * ·) g) = 0
  | 0, g => by simp [F]
  | 1, g => by
    simp [F, Fin.sum_univ_two, Fin.contractNth, hv]
  | n + 2, g => by
    have ih := F_coc u v hu hv n fun i => g i.succ.succ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h2 : ∀ j : Fin (n + 1), F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := fun j => by
      rw [F]
      congr 2
      funext i
      simp only [Fin.contractNth, Fin.val_succ, Nat.add_lt_add_iff_right,
        Nat.add_right_cancel_iff]
      rfl
    have h0 : F u v (n + 2) (Fin.contractNth 0 (· * ·) g) = u (g 0 * g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h1 : F u v (n + 2) (Fin.contractNth (Fin.succ 0) (· * ·) g) =
        u (g 0) (g 1 * g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h3 : F u v (n + 2) (fun i => g i.succ) = u (g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h4 : ∑ j : Fin (n + 1), (-1 : A) ^ ((j.succ.succ : ℕ) + 1) * F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) *
          F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2, Fin.val_succ, Fin.val_succ]; ring
    rw [h4, h0, h1, h3, eq_neg_of_add_eq_zero_right ih]
    simp only [Fin.val_zero, Fin.val_succ]
    linear_combination (F u v n fun i => g i.succ.succ.succ) * hu (g 0) (g 1) (g 2)

private theorem F_ins (u : K → K → A) (v : K → A) (hs : ∀ a b, u a b = u b a) (x : K) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    ∑ i : Fin (2 * E + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1) (Fin.insertNth (α := fun _ => K) i x g) =
      F u v (2 * E) g * v x := by
  intro E
  induction E with
  | zero =>
    intro g
    simp [F]
  | succ E ih =>
    intro g
    obtain ⟨a, b, rest, rfl⟩ : ∃ (a b : K) (rest : Fin (2 * E) → K),
        g = (Fin.cons a (Fin.cons b rest) : Fin (2 * E + 1 + 1) → K) := by
      let tail := Fin.tail (n := 2 * E + 1) (α := fun _ => K) g
      let rest := Fin.tail (n := 2 * E) (α := fun _ => K) tail
      refine ⟨g 0, tail 0, rest, ?_⟩
      calc
        g = Fin.cons (g 0) tail :=
          (Fin.cons_self_tail (α := fun _ => K) g).symm
        _ = Fin.cons (g 0) (Fin.cons (tail 0) rest) :=
          congrArg (Fin.cons (α := fun _ => K) (g 0))
            (Fin.cons_self_tail (α := fun _ => K) tail).symm
    have hpair (n : ℕ) (c d : K) (f : Fin n → K) :
        F u v (n + 2) (Fin.cons c (Fin.cons d f) : Fin (n + 2) → K) = u c d * F u v n f := by
      rw [F]
      simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
    change (∑ i : Fin (2 * E + 1 + 1 + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1 + 2)
      (Fin.insertNth (α := fun _ => K) i x (Fin.cons a (Fin.cons b rest)))) =
      F u v (2 * E + 2) (Fin.cons a (Fin.cons b rest)) * v x
    rw [hpair (2 * E) a b rest, Fin.sum_univ_succ, Fin.sum_univ_succ, mul_assoc (u a b),
      ← ih rest, Finset.mul_sum]
    simp only [Fin.insertNth_succ_cons, Fin.insertNth_zero', hpair, Fin.val_zero, Fin.val_succ, hs x a]
    rw [← add_assoc]
    refine (congrArg₂ (· + ·) (by ring : _ = (0 : A)) (Finset.sum_congr rfl fun j _ => by ring)).trans (zero_add _)

private theorem F_prod (u : K → K → A) (v : K → A) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    F u v (2 * E) g = ∏ s : Fin E, u (g ⟨2 * s, by omega⟩) (g ⟨2 * s + 1, by omega⟩)
  | 0, g => by simp [F]
  | E + 1, g => by
    rw [Fin.prod_univ_succ]
    exact congrArg (u _ _ * ·) (F_prod u v E fun i => g i.succ.succ)

private theorem ex_log [Finite K] [IsCyclic K] (q : ℕ) (ζ : K) (hζ : orderOf ζ = q) :
    ∃ (r : ℕ) (lg : K → ℤ), 0 < r ∧ (∀ a b, ((q * r : ℕ) : ℤ) ∣ lg a + lg b - lg (a * b)) ∧
      ∀ x : ℕ, ((q * r : ℕ) : ℤ) ∣ lg (ζ ^ x) - r * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := K)
  choose y hy using hg
  simp only at hy
  have hN : 0 < orderOf g := orderOf_pos g
  have hd : ∀ m n : ℕ, g ^ m = g ^ n → (orderOf g : ℤ) ∣ (m : ℤ) - n := fun m n h =>
    (pow_eq_pow_iff_modEq.1 h).symm.dvd
  set r := (orderOf g).gcd (y ζ) with hr
  have hr0 : 0 < r := Nat.gcd_pos_of_pos_left _ hN
  have hq : q * r = orderOf g := by
    rw [← hζ, ← congrArg orderOf (hy ζ), orderOf_pow, hr, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  have hb := Nat.gcd_eq_gcd_ab (orderOf g) (y ζ)
  refine ⟨r, fun a => (orderOf g).gcdB (y ζ) * y a, hr0, fun a b => ?_, fun x => ?_⟩
  · rw [hq]
    have := hd (y a + y b) (y (a * b)) (by rw [pow_add, hy, hy, hy])
    push_cast at this
    simpa [mul_sub, mul_add] using this.mul_left ((orderOf g).gcdB (y ζ))
  · rw [hq]
    have := hd (y (ζ ^ x)) (y ζ * x) (by rw [pow_mul, hy, hy])
    push_cast at this
    have h2 := (this.mul_left ((orderOf g).gcdB (y ζ))).sub (dvd_mul_right (orderOf g : ℤ) ((orderOf g).gcdA (y ζ) * x))
    refine h2.trans (dvd_of_eq ?_)
    rw [hr, hb]; ring

end UpperTheory.V.ZK.Coc

open UpperTheory.V.ZK.Coc in
theorem UpperTheory.V.ZK.sCoc : UpperTheory.V.ZK.SCoc := by
  intro k _ _ q _ e ζ hζ v
  obtain ⟨r, lg, hr, h1, h2⟩ := ex_log q ζ hζ.eq_orderOf.symm
  have hN : ((q * r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (NeZero.pos q) hr).ne'
  choose U hU using h1
  have hs : ∀ a b, U a b = U b a := fun a b => mul_left_cancel₀ hN (by rw [← hU, ← hU, mul_comm a b]; ring)
  have hc : ∀ a b c, U b c - U (a * b) c + U a (b * c) - U a b = 0 := fun a b c =>
    mul_left_cancel₀ hN (by simp only [mul_sub, mul_add, ← hU, mul_assoc a b c]; ring)
  set u : kˣ → kˣ → ZMod q := fun a b => (U a b : ZMod q) with hu
  set w : kˣ → ZMod q := fun a => Multiplicative.toAdd (v a) with hw
  refine ⟨Finsupp.linearCombination _ (F u w _), ?_, fun x g => ?_⟩
  · rintro _ ⟨z, rfl⟩
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
    | single g c =>
      have := F_coc u w (fun a b c => by simp only [hu]; exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) (hc a b c))
        (fun a b => by simp [hw]) _ g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [bd, Finsupp.linearCombination_single, map_smul, map_add (f := _), map_sum, one_smul, smul_eq_mul, one_mul]
      exact mul_eq_zero_of_right _ this
  · have key : ∑ j : ZMod q, u (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd j))
        (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd 1)) = x := by
      set χ := chi q ζ hζ.pow_eq_one x with hχ
      have e1 : ((q * r : ℕ) : ℤ) * ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          q * lg (χ (Multiplicative.ofAdd 1)) := by
        simp only [Finset.mul_sum, ← hU, ← map_mul, ← ofAdd_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have := Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) fun j => lg (χ (Multiplicative.ofAdd j))
        simp only [Equiv.coe_addRight] at this
        rw [this]; simp
      obtain ⟨m, hm⟩ := h2 (x * (1 : ZMod q).val)
      have e2 : lg (χ (Multiplicative.ofAdd 1)) = r * ((x * (1 : ZMod q).val : ℕ) + q * m) := by
        have : χ (Multiplicative.ofAdd 1) = ζ ^ (x * (1 : ZMod q).val) := rfl
        rw [this]; push_cast at hm ⊢; linear_combination hm
      have e3 : ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          (x * (1 : ZMod q).val : ℕ) + q * m := mul_left_cancel₀ hN (by rw [e1, e2]; push_cast; ring)
      have := congrArg (Int.cast : ℤ → ZMod q) e3
      simpa [hu] using this
    have hp : ∀ h : Fin (2 * e + 1 + 1) → kˣ, Finsupp.linearCombination (ZMod q) (F u w _)
        (prism (ZMod q) g _ (Finsupp.single h 1)) = F u w (2 * (e + 1)) h * w g := fun h => by
      rw [← F_ins u w (fun a b => by simp only [hu, hs a b]) g (e + 1) h]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [prism, Finsupp.linearCombination_single, one_smul, map_sum, map_smul, smul_eq_mul, mul_one, one_mul,
        inv_mul_cancel_comm, ite_self]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [zc, map_sum, cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hp, F_prod]
    rw [← Finset.sum_mul, ← key, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine congrArg (· * w g) (Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun s _ => ?_)
    have a1 : 2 * (s : ℕ) % 2 = 0 := by omega
    have a2 : ¬(2 * (s : ℕ) + 1) % 2 = 0 := by omega
    have a3 : 2 * (s : ℕ) / 2 = s := by omega
    simp only [a1, a2, a3, if_true, if_false, Fin.eta]

end
end

