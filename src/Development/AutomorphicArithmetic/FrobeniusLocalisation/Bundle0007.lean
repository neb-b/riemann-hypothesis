module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0002
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0006
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0004
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0005
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.CondRd
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem half_le_vd {φ : Frame} (H : HostAx φ) {l : ℕ} (hl : l.Prime) :
    (H.condE.factorization l : ℝ) ≤ 2 * H.vdH l := by
  have heN := (layer_bot H.toHostRaw hl (Nat.zero_le (H.condN.factorization l))).2.2
  rw [vd_formula H hl]
  have hnn : ∀ c : ℕ, (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · have h1 : (1 : ℝ) / c ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hc)]
        exact_mod_cast hc
      linarith
  have hhalf : ∀ c : ℕ, c ≠ 1 → (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
    intro c hc
    rcases c with _ | _ | c
    · norm_num
    · exact absurd rfl hc
    · have h1 : (1 : ℝ) / ((c + 1 + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
      linarith
  calc (H.condE.factorization l : ℝ)
      = 2 * ∑ j ∈ Finset.range (H.condE.factorization l), (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 2 * ∑ j ∈ Finset.range (H.condE.factorization l),
        (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
          (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro j hj
        apply hhalf
        rw [Ne, Subgroup.card_eq_one]
        have hjN : j ≤ H.condN.factorization l := (Finset.mem_range.1 hj).le.trans heN
        rw [(layer_bot H.toHostRaw hl hjN).1]
        exact not_le.2 (Finset.mem_range.1 hj)
    _ ≤ 2 * ∑ j ∈ Finset.range (H.condN.factorization l),
        (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
          (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 heN)
          (fun j _ _ => hnn _)

theorem UpperTheory.HF.cond_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.rd ≤ H.condE ∧ Real.log H.rd ≤ Real.log H.condE ∧ Real.log H.condE ≤ Real.log H.condN ∧ (H.condE : ℝ) ≤ H.rd ^ 2 ∧ 4 * φ.ord ≤ H.condE.totient ∧ 4 * φ.ord ∣ H.condE.totient ∧ 4 * φ.ord ≤ H.condE := by
  intro φ H
  obtain ⟨hEN, hE0, hspec⟩ := condE_spec H.toHostRaw
  have hN0 := H.condN_ne_zero
  obtain ⟨-, hlogrd, -, hrd0⟩ := log_rd_sum H
  have hE0' : (0 : ℝ) < H.condE := by exact_mod_cast hE0
  have logE : Real.log H.condE =
      ∑ l ∈ H.condN.primeFactors, (H.condE.factorization l : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    apply Finset.sum_subset (Nat.primeFactors_mono hEN hN0)
    intro l _ hl
    have h0 : H.condE.factorization l = 0 := by
      rwa [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hl
    simp [h0]
  have hb : Real.log H.rd ≤ Real.log H.condE := by
    rw [hlogrd, logE]
    apply Finset.sum_le_sum
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    exact mul_le_mul_of_nonneg_right (vd_le H hlp).2
      (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))
  have hd : Real.log H.condE ≤ 2 * Real.log H.rd := by
    rw [hlogrd, logE, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (half_le_vd H hlp)
      (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))
  have ha : H.rd ≤ H.condE := (Real.log_le_log_iff hrd0 hE0').1 hb
  have hcE : (H.condE : ℝ) ≤ H.rd ^ 2 := by
    rw [← Real.log_le_log_iff hE0' (by positivity), Real.log_pow]
    push_cast
    linarith
  have hc : Real.log H.condE ≤ Real.log H.condN :=
    Real.log_le_log hE0' (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hEN)
  have htop : UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw 1 = ⊤ := by
    ext g
    simp only [Subgroup.mem_top, iff_true]
    obtain ⟨u, rfl⟩ := H.der.art_surj g
    exact (UpperTheory.HF.Formalism.HC.HostRaw.mem_imgOne H.toHostRaw (one_dvd _) _).2 ⟨u, Nat.modEq_one, rfl⟩
  have hbot : UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw H.condE = ⊥ := (hspec _ hEN).2 dvd_rfl
  have hdvd := card_imgOne_dvd H.toHostRaw (one_dvd H.condE) hEN
  rw [htop, hbot, Subgroup.card_top, Subgroup.card_bot, Nat.totient_one, Nat.div_one, one_mul,
    (φ.hostGroup).1] at hdvd
  have htpos : 0 < H.condE.totient := Nat.totient_pos.2 hE0
  exact ⟨ha, hb, hc, hcE, Nat.le_of_dvd htpos hdvd, hdvd,
    (Nat.le_of_dvd htpos hdvd).trans (Nat.totient_le _)⟩
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rad_bounds :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rad ≤ 2 * Real.log H.rd ∧ (H.ram.card : ℝ) ≤ 2 * Real.log H.rd / Real.log 2 ∧ (∀ D₀ : ℝ, 0 ≤ D₀ → ∑ l ∈ H.ram, (⌈H.vdH l * D₀⌉ : ℝ) * Real.log l ≤ (D₀ + 2) * Real.log H.rd) ∧ ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ) ≤ H.rd ^ 2 ∧ ∀ g₁ g₂ L : ℝ, 0 < g₁ → 0 < g₂ → Real.log g₁ ≤ 9 * L + 1 → Real.log g₂ ≤ 9 * L + 1 → Real.log H.rd ≤ L / 100 → Real.log (g₁ * g₂ * H.rad) ≤ Real.log (g₁ * g₂) + 2 * Real.log H.rd ∧ Real.log (g₁ * g₂) + 2 * Real.log H.rd ≤ 18 * L + 2 + L / 50 := by
  intro φ H
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have hp : ∀ l ∈ H.ram, l.Prime := fun l hl => Nat.prime_of_mem_primeFactors hl
  have hv : ∀ l ∈ H.ram, 1 / 2 ≤ H.vdH l := fun l hl => (UpperTheory.HF.mem_ram H (hp l hl)).2.2.2.1 hl
  have hl0 : ∀ l ∈ H.ram, (0 : ℝ) < l := fun l hl => Nat.cast_pos.2 (hp l hl).pos
  have hlog2 : ∀ l ∈ H.ram, Real.log 2 ≤ Real.log l := fun l hl =>
    Real.log_le_log (by norm_num) (by exact_mod_cast (hp l hl).two_le)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ∀ l ∈ H.ram, 0 ≤ Real.log l := fun l hl => h2.le.trans (hlog2 l hl)
  have hsum : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd := by
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    nlinarith [hv l hl, hlog l hl]
  have hradpos : (0 : ℝ) < H.rad := by
    unfold HostRaw.rad
    rw [Nat.cast_prod]
    exact Finset.prod_pos hl0
  have h1 : Real.log H.rad ≤ 2 * Real.log H.rd := by
    refine le_trans (le_of_eq ?_) hsum
    unfold HostRaw.rad
    rw [Nat.cast_prod, Real.log_prod fun l hl => (hl0 l hl).ne']
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2]
    refine le_trans ?_ hsum
    have := Finset.card_nsmul_le_sum H.ram (fun l : ℕ => Real.log l) _ hlog2
    simpa using this
  · intro D₀ hD
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hc : (⌈H.vdH l * D₀⌉ : ℝ) ≤ (D₀ + 2) * H.vdH l := by
      have := (Int.ceil_lt_add_one (H.vdH l * D₀)).le
      nlinarith [hv l hl]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hc (hlog l hl)
  · have hpos : (0 : ℝ) < ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_pos fun l hl => by
        rw [Nat.cast_pow]; exact pow_pos (hl0 l hl) _
    rw [← Real.log_le_log_iff hpos (pow_pos hrd 2), Real.log_pow, Nat.cast_prod,
      Real.log_prod fun l hl => by rw [Nat.cast_pow]; exact (pow_pos (hl0 l hl) _).ne', hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Nat.cast_pow, Real.log_pow, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (hlog l hl)
    have hy := hv l hl
    push_cast
    by_cases h : H.vdH l ≤ 1
    · have : ⌈H.vdH l⌉₊ ≤ 1 := Nat.ceil_le.2 (by simpa using h)
      have : (⌈H.vdH l⌉₊ : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    · have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ H.vdH l)).le
      push Not at h
      linarith
  · intro g₁ g₂ L h₁ h₂ hg₁ hg₂ hL
    constructor
    · rw [Real.log_mul (mul_pos h₁ h₂).ne' hradpos.ne']
      linarith
    · rw [Real.log_mul h₁.ne' h₂.ne']
      linarith
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.VdTameWild
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem half_le {c : ℕ} (h : 2 ≤ c) : (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
  have h2 : (2 : ℝ) ≤ c := by exact_mod_cast h
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2
  linarith

private theorem term_nonneg {c : ℕ} (h : 0 < c) : (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
  have hc : (1 : ℝ) ≤ c := by exact_mod_cast h
  have h1 : 1 / (c : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hc
  linarith

theorem UpperTheory.HF.vd_tame_wild :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (¬ l ∣ H.el l → H.vdH l = 1 - 1 / (H.el l : ℝ)) ∧ (l ∣ H.el l → 1 ≤ H.vdH l) ∧ (¬ l ∣ H.el l → H.sl l = 1) := by
  intro φ H l hl
  set v := H.condN.factorization l with hv
  set e := (HostRaw.condE H.toHostRaw).factorization l with he
  let G : ℕ → Subgroup φ.GG := fun j => HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ j)
  have hev : e ≤ v := (layer_bot H.toHostRaw (j := 0) hl (Nat.zero_le _)).2.2
  have hbot : ∀ j, j ≤ v → (G j = ⊥ ↔ e ≤ j) := fun j hj => (layer_bot H.toHostRaw hl hj).1
  have hdvd : ∀ j, j ≤ e → Nat.card (G j) ∣ (l ^ e).totient / (l ^ j).totient :=
    fun j hj => (layer_bot H.toHostRaw hl (hj.trans hev)).2.1 hj
  have hcard_one : ∀ j, j ≤ v → (Nat.card (G j) = 1 ↔ e ≤ j) :=
    fun j hj => Subgroup.card_eq_one.trans (hbot j hj)
  have hpos : ∀ j, j ≤ v → 0 < Nat.card (G j) := by
    intro j hjv
    by_cases hje : j ≤ e
    · have h1 : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
      have h2 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      have h3 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      exact Nat.pos_of_dvd_of_pos (hdvd j hje) (Nat.div_pos (Nat.le_of_dvd h3 h1) h2)
    · push_neg at hje
      rw [(hcard_one j hjv).2 hje.le]
      exact Nat.one_pos
  have hge : ∀ j, j < e → 2 ≤ Nat.card (G j) := by
    intro j hj
    have hjv : j ≤ v := by omega
    have h1 := hpos j hjv
    have h2 : Nat.card (G j) ≠ 1 := fun h => by
      have := (hcard_one j hjv).1 h
      omega
    omega
  have hanti : 1 ≤ v → Nat.card (G 1) ∣ Nat.card (G 0) := by
    intro h1v
    apply Subgroup.card_dvd_of_le
    apply HostRaw.imgOne_anti _ (mul_dvd_mul_left _ (pow_dvd_pow l (by norm_num)))
    calc H.condN / l ^ v * l ^ 1 ∣ H.condN / l ^ v * l ^ v := mul_dvd_mul_left _ (pow_dvd_pow l h1v)
      _ = H.condN := Nat.div_mul_cancel (Nat.ordProj_dvd _ _)
  have hel : H.el l = Nat.card (G 0) := by
    show Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v)) =
      Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ 0))
    rw [pow_zero, mul_one]
  have hsum : H.vdH l = ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) := vd_formula H hl
  have hsl : H.sl l = max 1 e := rfl
  have key1 : ¬ l ∣ H.el l → e ≤ 1 := by
    intro hnd
    by_contra hlt
    push_neg at hlt
    have h1v : 1 ≤ v := by omega
    have hd := hdvd 1 hlt.le
    rw [Nat.totient_prime_pow hl (by omega), pow_one, Nat.totient_prime hl,
      Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hl.one_lt)] at hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hl).1 hd
    have hne : Nat.card (G 1) ≠ 1 := fun h => by
      have := (hcard_one 1 h1v).1 h
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hk')
    have hl1 : l ∣ Nat.card (G 1) := hk' ▸ dvd_pow_self l hk0
    exact hnd (hel ▸ hl1.trans (hanti h1v))
  have key2 : l ∣ H.el l → 2 ≤ e := by
    intro hd
    rw [hel] at hd
    by_contra hlt
    have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with h0 | h1
    · rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)] at hd
      exact hl.not_dvd_one hd
    · have hd0 := hdvd 0 (by omega)
      rw [h1] at hd0
      simp [Nat.totient_prime hl] at hd0
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hl.one_lt) (hd.trans hd0)
      have := hl.two_le
      omega
  refine ⟨fun hnd => ?_, fun hd => ?_, fun hnd => ?_⟩
  · have he1 := key1 hnd
    rw [hsum, hel]
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j hj hj0
      have hjv : j ≤ v := (Finset.mem_range.1 hj).le
      rw [(hcard_one j hjv).2 (by omega)]
      norm_num
    · intro h0
      have hv0 : v = 0 := by simpa using h0
      rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)]
      norm_num
  · rw [hsum]
    have h2e := key2 hd
    have h2v : 2 ≤ v := h2e.trans hev
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have h01 : (0 : ℕ) ≠ 1 := by norm_num
    calc (1 : ℝ) = 1 / 2 + 1 / 2 := by norm_num
      _ ≤ (1 - 1 / (Nat.card (G 0) : ℝ)) + (1 - 1 / (Nat.card (G 1) : ℝ)) :=
          add_le_add (half_le (hge 0 (by omega))) (half_le (hge 1 (by omega)))
      _ = ∑ j ∈ ({0, 1} : Finset ℕ), (1 - 1 / (Nat.card (G j) : ℝ)) :=
          (Finset.sum_pair (f := fun j => (1 - 1 / (Nat.card (G j) : ℝ))) h01).symm
      _ ≤ ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j hj _ => term_nonneg (hpos j (Finset.mem_range.1 hj).le))
  · rw [hsl]
    exact max_eq_left (key1 hnd)
end

