module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.CommOfBounded
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

def IsKv (b : ℤ) (d : ℕ) (lam : ℂ) (v : m → ℂ) : Prop := ∀ i, IsK b d (v i / lam)

lemma cmL_omega1 : (cmL a b d ha hd lam hlam).ω₁ = lam * a := rfl
lemma cmL_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl

lemma mem_stdLat_iff (L : PeriodPair) (v : m → ℂ) : v ∈ stdLat L m ↔ ∀ i, v i ∈ L.lattice := by
  simp only [PI.ULS.stdLat, AddSubgroup.mem_pi, Set.mem_univ, forall_const,
    Submodule.mem_toAddSubgroup]

private theorem mul_div_cancel_left_of_ne_zero {w : ℂ} (hw : w ≠ 0) (x : ℂ) : w * x / w = x := by
  rw [mul_comm, mul_div_assoc, div_self hw, mul_one]

private theorem mem_cmL_lattice_iff (z : ℂ) :
    z ∈ (PI.ULS.cmL a b d ha hd lam hlam).lattice ↔
      ∃ p q : ℤ, z = lam * ((p : ℂ) * a + q * PI.ULS.cmTheta b d) := by
  rw [lattice_iff]
  simp only [cmL_omega1, cmL_omega2, Complex.real_smul, Complex.ofReal_intCast]
  constructor
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩

lemma isKv_of_mem {s : m → ℂ} (hs : s ∈ stdLat (cmL a b d ha hd lam hlam) m) : IsKv b d lam s := by
  intro i
  obtain ⟨p, q, hpq⟩ := (mem_cmL_lattice_iff _).1 ((mem_stdLat_iff _ s).1 hs i)
  refine ⟨p * (a : ℤ), q, 1, one_ne_zero, ?_⟩
  rw [hpq, mul_div_cancel_left_of_ne_zero hlam]
  push_cast
  ring

private theorem natCast_smul_eq_nsmul (N : ℕ) (y : m → ℂ) : (N : ℂ) • y = N • y := by
  exact Nat.cast_smul_eq_nsmul ℂ N y

private theorem nsmul_apply_eq_natCast_mul (N : ℕ) (v : m → ℂ) (i : m) : (N • v) i = (N : ℂ) * v i := by
  rw [← natCast_smul_eq_nsmul, Pi.smul_apply, smul_eq_mul]

lemma exists_nsmul_mem {v : m → ℂ} (h : IsKv b d lam v) :
    ∃ N : ℕ, N ≠ 0 ∧ N • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose p q r hr hpq using h
  have hself : ∀ z : ℤ, z ∣ (z.natAbs : ℤ) := fun _ => Int.dvd_natAbs.mpr dvd_rfl
  obtain ⟨M, hM0, hMdvd⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ i, r i ∣ (M : ℤ) := by
    refine ⟨∏ j, (r j).natAbs, Finset.prod_ne_zero_iff.mpr fun j _ => Int.natAbs_ne_zero.mpr (hr j),
      fun i => (hself (r i)).trans ?_⟩
    have hi : (r i).natAbs ∣ ∏ j, (r j).natAbs :=
      Finset.dvd_prod_of_mem (fun j => (r j).natAbs) (Finset.mem_univ i)
    exact Int.natCast_dvd_natCast.mpr hi
  refine ⟨a * M, mul_ne_zero ha.ne' hM0, ?_⟩
  rw [mem_stdLat_iff]
  intro i
  obtain ⟨k, hk⟩ := hMdvd i
  have hk' : (M : ℂ) = (r i : ℂ) * k := by exact_mod_cast hk
  have e : v i = v i / lam * lam := (div_eq_iff hlam).mp rfl
  have hv : (r i : ℂ) * v i = lam * (p i + q i * PI.ULS.cmTheta b d) := by
    calc (r i : ℂ) * v i = (r i * (v i / lam)) * lam := by rw [mul_assoc, ← e]
      _ = (p i + q i * PI.ULS.cmTheta b d) * lam := by rw [hpq i]
      _ = lam * (p i + q i * PI.ULS.cmTheta b d) := mul_comm _ _
  rw [mem_cmL_lattice_iff]
  refine ⟨k * p i, a * k * q i, ?_⟩
  rw [nsmul_apply_eq_natCast_mul, Nat.cast_mul, hk']
  push_cast
  linear_combination ((a : ℂ) * k) * hv

lemma isKv_of_nsmul {v : m → ℂ} {N : ℕ} (hN : N ≠ 0) (h : IsKv b d lam (N • v)) : IsKv b d lam v := by
  intro i
  obtain ⟨p, q, r, hr, h'⟩ := h i
  refine ⟨p, q, r * N, mul_ne_zero hr (by exact_mod_cast hN), ?_⟩
  rw [← h', nsmul_apply_eq_natCast_mul]
  push_cast
  ring

lemma isKv_sub {v w : m → ℂ} (hv : IsKv b d lam v) (hw : IsKv b d lam w) : IsKv b d lam (v - w) := by
  intro i
  rw [Pi.sub_apply, sub_div]
  exact isK_sub (hv i) (hw i)

lemma isKv_smul {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) {t : ℂ} {v : m → ℂ}
    (ht : IsK b d t) (hv : IsKv b d lam v) : IsKv b d lam (t • v) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  exact isK_mul hn ht (hv i)

lemma isKv_single {w : ℂ} (hw : IsK b d (w / lam)) (i : m) : IsKv b d lam (Pi.single i w) := by
  intro j
  rw [Pi.single_apply]
  split_ifs
  · exact hw
  · rw [zero_div]
    exact ⟨0, 0, 1, one_ne_zero, by simp⟩

def kappa (L : PeriodPair) (lam : ℂ) : ℂ := lam * conj lam * ((area L : ℝ) : ℂ)⁻¹

lemma kappa_conj (L : PeriodPair) (lam : ℂ) : conj (kappa L lam) = kappa L lam := by
  simp only [kappa]
  rw [map_mul, map_mul, map_inv₀, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma kappa_ne (L : PeriodPair) (hlam : lam ≠ 0) : kappa L lam ≠ 0 := by
  have harea : ((area L : ℝ) : ℂ) ≠ 0 := by
    rw [area_eq]
    exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (detD_ne L))
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  simp only [kappa]
  exact mul_ne_zero (mul_ne_zero hlam hc) (inv_ne_zero harea)

lemma stdH_kappa (L : PeriodPair) (hlam : lam ≠ 0) (x y : m → ℂ) :
    stdH L m x y = kappa L lam * ∑ i, (x i / lam) * conj (y i / lam) := by
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  have h1 : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  have h2 : conj lam * (conj lam)⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [stdH_apply]
  simp only [kappa]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_div₀]
  linear_combination (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹) * (conj lam * (conj lam)⁻¹)) * h1 +
    (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹)) * h2

lemma isK_H {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) (L : PeriodPair) (hlam : lam ≠ 0)
    {x y : m → ℂ} (hx : IsKv b d lam x) (hy : IsKv b d lam y) :
    ∃ t, IsK b d t ∧ stdH L m x y = kappa L lam * t :=
  ⟨∑ i, (x i / lam) * conj (y i / lam),
    isK_sum hn _ _ fun i _ => isK_mul hn (hx i) (isK_conj (hy i)),
    stdH_kappa L hlam x y⟩

private theorem intCast_smul_eq_zsmul (p : ℤ) (y : m → ℂ) : (p : ℂ) • y = p • y := by
  exact Int.cast_smul_eq_zsmul ℂ p y

private theorem nsmul_intCast_smul_comm (N : ℕ) (p : ℤ) (y : m → ℂ) : N • ((p : ℂ) • y) = p • (N • y) := by
  rw [← natCast_smul_eq_nsmul N ((p : ℂ) • y), ← natCast_smul_eq_nsmul N y, smul_comm (N : ℂ) (p : ℂ) y,
    intCast_smul_eq_zsmul p ((N : ℂ) • y)]

private theorem nsmul_mem_of_dvd_of_nsmul_mem {S : AddSubgroup (m → ℂ)} {x : m → ℂ} {n N : ℕ} (hnN : n ∣ N)
    (hx : n • x ∈ S) : N • x ∈ S := by
  obtain ⟨k, rfl⟩ := hnN
  have e : (n * k) • x = k • (n • x) := by
    calc (n * k) • x = ((n * k : ℕ) : ℂ) • x := (natCast_smul_eq_nsmul _ _).symm
      _ = (k : ℂ) • (n : ℂ) • x := by rw [smul_smul, Nat.cast_mul, mul_comm]
      _ = k • n • x := by rw [natCast_smul_eq_nsmul, natCast_smul_eq_nsmul]
  rw [e]
  exact nsmul_mem hx k

lemma bounded_map (φ : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (h1 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₁)))
    (h2 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₂))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m,
      N • φ s ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose N1 hN1 hm1 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h1 i)
  choose N2 hN2 hm2 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h2 i)
  refine ⟨∏ j, N1 j * N2 j, Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero (hN1 j) (hN2 j), ?_⟩
  have hdvd : ∀ i, N1 i * N2 i ∣ ∏ j, N1 j * N2 j := fun i =>
    Finset.dvd_prod_of_mem (fun j => N1 j * N2 j) (Finset.mem_univ i)
  have k1 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_right (N1 i) (N2 i)).trans (hdvd i)) (hm1 i)
  have k2 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_left (N2 i) (N1 i)).trans (hdvd i)) (hm2 i)
  intro s hs
  have hs' := (mem_stdLat_iff _ s).1 hs
  choose p q hpq using fun i => (lattice_iff _ _).1 (hs' i)
  have hs_sum : s = ∑ i, Pi.single i (s i) := by
    exact (Finset.univ_sum_single s).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs_sum, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have e : Pi.single i (s i) = ((p i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ +
      ((q i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ := by
    rw [hpq i]
    funext j
    by_cases h : j = i
    · subst h
      simp [Complex.real_smul]
    · simp [Pi.single_apply, h]
  rw [e, map_add (f := _), map_smul, map_smul, smul_add, nsmul_intCast_smul_comm, nsmul_intCast_smul_comm]
  exact add_mem (zsmul_mem (k1 i) _) (zsmul_mem (k2 i) _)

lemma comm_of_bounded (σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (h1 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N • σ s ∈ stdLat (cmL a b d ha hd lam hlam) m)
    (h2 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N' • σ.symm s ∈ stdLat (cmL a b d ha hd lam hlam) m) :
    relIdx (stdLat (cmL a b d ha hd lam hlam) m)
        (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m))
        (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 := by
  unfold PI.ULS.relIdx PI.ULS.imgLat
  refine ⟨?_, ?_⟩
  · rw [← AddSubgroup.relIndex_comap]
    refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    rw [AddSubgroup.mem_comap]
    show σ ((N : ℂ) • s) ∈ _
    rw [map_smul, natCast_smul_eq_nsmul]
    exact h1 s hs
  · refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN')
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine AddSubgroup.mem_map.mpr ⟨N' • σ.symm s, h2 s hs, ?_⟩
    show σ (N' • σ.symm s) = (N' : ℂ) • s
    rw [map_nsmul, LinearEquiv.apply_symm_apply, natCast_smul_eq_nsmul]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.DescentStep
section
noncomputable section
open scoped ComplexConjugate
open Polynomial

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

lemma pigeon {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (A B E : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (hB : ¬ (p : ℤ) ∣ B) : ∃ s t : ℤ, (p : ℤ) ∣ s ^ 2 * A + t ^ 2 * B - E := by
  have := Fact.mk hp
  have hA' : (A : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hB' : (B : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf : (C (A : ZMod p) * X ^ 2 - C (E : ZMod p)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hA']; norm_num), degree_C_mul_X_pow 2 hA']
    rfl
  have hg : (C (B : ZMod p) * X ^ 2).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hB']
    rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg (by rw [ZMod.card]; exact hodd)
  refine ⟨(x.val : ℤ), (y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  linear_combination hxy

variable {a : ℕ} {b c : ℤ} {d : ℕ}

lemma descent_step (hok : CmOK a b c d) {P Q r p q : ℤ} (hr : (d : ℤ) ∣ r) (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hM : r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q) :
    (d : ℤ) ∣ P ∧ (d : ℤ) ∣ Q := by
  obtain ⟨h4, -, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set N := P ^ 2 + P * Q * b + Q ^ 2 * (a * c) with hNdef
  have hcop : IsCoprime ((d : ℤ) ^ 2) q :=
    IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hD.irreducible).mpr hq)
  have hdN : (d : ℤ) ^ 2 ∣ N := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hM]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hr 2) _
  have hid : 4 * N = (2 * P + b * Q) ^ 2 + d * Q ^ 2 := by
    rw [hNdef]
    linear_combination Q ^ 2 * h4
  have hX : (d : ℤ) ∣ 2 * P + b * Q := by
    apply hD.dvd_of_dvd_pow (n := 2)
    have : (2 * P + b * Q) ^ 2 = 4 * N - d * Q ^ 2 := by rw [hid]; ring
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left (dvd_trans (dvd_pow_self _ two_ne_zero) hdN) _) (dvd_mul_right _ _)
  have hQ2 : (d : ℤ) ∣ Q ^ 2 := by
    have h1 : (d : ℤ) ^ 2 ∣ d * Q ^ 2 := by
      have : (d : ℤ) * Q ^ 2 = 4 * N - (2 * P + b * Q) ^ 2 := by rw [hid]; ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hdN _) (pow_dvd_pow_of_dvd hX 2)
    rw [pow_two] at h1
    exact (mul_dvd_mul_iff_left hD0).mp h1
  have hQ : (d : ℤ) ∣ Q := hD.dvd_of_dvd_pow hQ2
  have h2P : (d : ℤ) ∣ 2 * P := by
    have : 2 * P = (2 * P + b * Q) - b * Q := by ring
    rw [this]
    exact dvd_sub hX (Dvd.dvd.mul_left hQ _)
  refine ⟨?_, hQ⟩
  rcases hD.dvd_or_dvd h2P with h | h
  · exact absurd h hD2
  · exact h

lemma norm_square (hok : CmOK a b c d) {γ : ℂ} (hγ : IsK b d γ) {p q : ℤ} (hp : ¬ (d : ℤ) ∣ p)
    (hq : ¬ (d : ℤ) ∣ q) (hN : γ * conj γ = (p : ℂ) / q) : ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
  obtain ⟨h4, ha, h8, hdp⟩ := hok
  have hD : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
  have hD0 : (d : ℤ) ≠ 0 := hD.ne_zero
  have hD2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h' : d ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq (dvd_zero _)
  have hθ : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c := by
    have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    have h4' : (4 * a * c : ℂ) = b ^ 2 + d := by exact_mod_cast h4
    unfold cmTheta
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs +
      (-1 / 4 : ℂ) * h4'

  have rel : ∀ P Q r : ℤ, (r : ℂ) * γ = P + Q * cmTheta b d →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
    intro P Q r hr
    have h1 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = r ^ 2 * ((p : ℂ) / q) := by
      rw [map_mul, map_intCast, ← hN]
      ring
    have h2 : (r : ℂ) * γ * conj ((r : ℂ) * γ) = P ^ 2 + P * Q * b + Q ^ 2 * (a * c) := by
      rw [hr, map_add (f := _), map_mul, map_intCast, map_intCast, theta_conj]
      linear_combination (Q : ℂ) ^ 2 * hθ
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hC : (r : ℂ) ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q := by
      rw [← h2, h1]
      field_simp
    exact_mod_cast hC

  have main : ∀ n : ℕ, ∀ P Q r : ℤ, r.natAbs = n → r ≠ 0 →
      r ^ 2 * p = (P ^ 2 + P * Q * b + Q ^ 2 * (a * c)) * q → ∃ s : ℤ, (d : ℤ) ∣ s ^ 2 * q - p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q r hn hr0 hM
      by_cases hdr : (d : ℤ) ∣ r
      · obtain ⟨hP, hQ⟩ := descent_step ⟨h4, ha, h8, hdp⟩ hdr hp hq hM
        obtain ⟨P', rfl⟩ := hP
        obtain ⟨Q', rfl⟩ := hQ
        obtain ⟨r', rfl⟩ := hdr
        have hr' : r' ≠ 0 := by
          rintro rfl
          simp at hr0
        have hM' : r' ^ 2 * p = (P' ^ 2 + P' * Q' * b + Q' ^ 2 * (a * c)) * q := by
          have hd2 : ((d : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 hD0
          apply mul_left_cancel₀ hd2
          linear_combination hM
        refine ih r'.natAbs ?_ P' Q' r' rfl hr' hM'
        rw [← hn, Int.natAbs_mul]
        have h1 : 1 < (d : ℤ).natAbs := by
          have := hdp.two_le
          simp only [Int.natAbs_natCast]
          omega
        have h2 : 0 < r'.natAbs := Int.natAbs_pos.mpr hr'
        nlinarith
      · have := Fact.mk hdp
        have hkey : (2 * r) ^ 2 * p = (2 * P + b * Q) ^ 2 * q + d * (Q ^ 2 * q) := by
          linear_combination 4 * hM + q * Q ^ 2 * h4
        have h2r : ((2 * r : ℤ) : ZMod d) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          intro h
          rcases hD.dvd_or_dvd h with h | h
          · exact hD2 h
          · exact hdr h
        refine ⟨((((2 * P + b * Q : ℤ) : ZMod d) * ((2 * r : ℤ) : ZMod d)⁻¹).val : ℤ), ?_⟩
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hk := congrArg (Int.cast : ℤ → ZMod d) hkey
        push_cast at hk h2r ⊢
        rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero] at *
        have hinv : (2 * (r : ZMod d))⁻¹ ^ 2 * (2 * (r : ZMod d)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ h2r, one_pow]
        linear_combination (-((2 * (r : ZMod d))⁻¹ ^ 2)) * hk + (p : ZMod d) * hinv
  obtain ⟨P, Q, r, hr0, hr⟩ := hγ
  exact main r.natAbs P Q r rfl hr0 (rel P Q r hr)

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepExact
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Helpers

theorem rep_H_nsmul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (M : ℕ) (z : m → ℂ) :
    stdH L m (M • z) (M • z) = (M : ℂ) ^ 2 * stdH L m z z := by
  simp only [map_nsmul, LinearMap.smul_apply]
  simp only [nsmul_eq_mul]
  ring

end Helpers

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepNewton
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_H_smul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (z : m → ℂ) :
    stdH L m (ξ • z) (ξ • z) = ξ * conj ξ * stdH L m z z := by
  rw [LinearMap.map_smul₂, LinearMap.map_smulₛₗ]
  simp only [smul_eq_mul]
  ring

theorem rep_tau {m : Type} (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {l : ℕ} (hl : l.Prime) :
    ∃ τ : ℂ, ∃ r s : ℤ, τ + conj τ = 1 ∧ τ * conj τ = (r : ℂ) / s ∧ ¬ (l : ℤ) ∣ s ∧
      ∀ v : m → ℂ, SatMem l Λ v → SatMem l Λ (τ • v) := by
  obtain ⟨hac, -, hd8, -⟩ := hOK
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := by
    rcases Int.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have h4 : (d : ℤ) = 4 * ((a : ℤ) * c - j * j) := by
        rw [hj] at hac
        linear_combination -hac
      generalize (a : ℤ) * c - j * j = t at h4
      omega
    · exact ⟨j, hj⟩
  have hadd := rep_theta_add_conj b d
  have hmul := rep_theta_mul_conj a b c d hac
  refine ⟨cmTheta b d - (k : ℂ), a * c - k * b + k ^ 2, 1, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_intCast]
    have hb : (b : ℂ) = 2 * k + 1 := by
      rw [hk]
      push_cast
      ring
    linear_combination hadd + hb
  · rw [map_sub, map_intCast]
    push_cast
    rw [div_one]
    linear_combination hmul - (k : ℂ) * hadd
  · intro h
    have h1 := Int.le_of_dvd one_pos h
    have h2 := hl.one_lt
    omega
  · intro v hv
    unfold SatMem at hv ⊢
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n, hn, ?_⟩
    rw [smul_comm, sub_smul, Int.cast_smul_eq_zsmul]
    exact Λ.sub_mem (hθ _ hnv) (Λ.zsmul_mem hnv k)

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

