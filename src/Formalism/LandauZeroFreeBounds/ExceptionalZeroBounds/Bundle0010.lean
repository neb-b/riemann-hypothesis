module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem prod_one_sub_inv_ge_inv_card_succ (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hsub : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs p hp, ha p hp⟩
    have hcard : s.card + 2 ≤ a := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h1
      omega
    have hc : (insert a s).card = s.card + 1 := by simp [has]
    rw [Finset.prod_insert has, hc]
    push_cast
    have ih' := ih hs
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha' : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast hcard
    have hk : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) ≤ 1 - 1 / (a : ℝ) := by
      have h1 : (1 : ℝ) / a ≤ 1 := by rw [div_le_one ha0]; linarith
      linarith
    have e1 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) - 1 / ((s.card : ℝ) + 1 + 1) =
        ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) := by
      field_simp
      ring
    have e2 : 0 ≤ ((a : ℝ) - ((s.card : ℝ) + 2)) /
        ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) :=
      div_nonneg (by linarith) (by positivity)
    have e3 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left ih' hpos
    linarith

theorem changeLevel_eq_of_agree_coprime {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) :
    DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁ =
      DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ := by
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  ext a
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.cast_eq_val, ZMod.cast_eq_val]
  exact h _ (ZMod.val_coe_unit_coprime a)

theorem euler_factor_term_norm_le {M : ℕ} (φ : DirichletCharacter ℂ M) (p : ℕ) :
    ‖φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 / (p : ℝ) := by
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have h1 : ‖(p : ℂ) ^ (-(1 : ℂ))‖ = 1 / (p : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hp]
      simp [Real.rpow_neg_one]
    rw [h1]
    exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one φ _)

theorem euler_factor_product_upper {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ) :
    ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [euler_factor_term_norm_le φ p]

theorem euler_factor_product_lower {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  · have h1 := euler_factor_term_norm_le φ p
    have h2 := norm_sub_norm_le (1 : ℂ) (φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))
    rw [norm_one] at h2
    linarith

theorem prod_one_add_mul_one_sub_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, (1 + 1 / (p : ℝ))) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one₀ (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  · have h2 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    nlinarith

theorem lfunction_one_same_character : SameCharacterLFunctionOne := by
  intro q₁ q _ _ χ₁ χ hχ₁ hχ h
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hS : ∀ p ∈ (q₁ * q).primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hL₁ := DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q) χ₁ (s := 1)
    (Or.inl hχ₁)
  have hL := DirichletCharacter.LFunction_changeLevel (dvd_mul_left q q₁) χ (s := 1) (Or.inl hχ)
  rw [changeLevel_eq_of_agree_coprime χ₁ χ h, hL] at hL₁
  have hnorm : ‖DirichletCharacter.LFunction χ₁ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ =
      ‖DirichletCharacter.LFunction χ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
    rw [← norm_mul, ← norm_mul, hL₁]
  have hlow := euler_factor_product_lower χ₁ _ hS
  have hup := euler_factor_product_upper χ (q₁ * q).primeFactors
  have hge := prod_one_sub_inv_ge_inv_card_succ _ hS
  have hAB := prod_one_add_mul_one_sub_le_one _ hS
  have hk : (0 : ℝ) < ((q₁ * q).primeFactors.card : ℝ) + 1 := by positivity
  have hA0 : (0 : ℝ) ≤ ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hB' : 1 ≤ (∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
      (((q₁ * q).primeFactors.card : ℝ) + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hge hk.le
    rwa [one_div, inv_mul_cancel₀ hk.ne'] at h1
  have hx := norm_nonneg (DirichletCharacter.LFunction χ₁ 1)
  have hy := norm_nonneg (DirichletCharacter.LFunction χ 1)
  have h1 : ‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ)) ≤
      ‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) := by
    calc _ ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ *
          ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ :=
          mul_le_mul_of_nonneg_left hlow hx
      _ = _ := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hup hy
  have hA : ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) ≤
      ((q₁ * q).primeFactors.card : ℝ) + 1 := by nlinarith
  calc ‖DirichletCharacter.LFunction χ₁ 1‖
        ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ * ((∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1)) := le_mul_of_one_le_right hx hB'
    _ = (‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := by ring
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := mul_le_mul_of_nonneg_right h1 hk.le
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * (((q₁ * q).primeFactors.card : ℝ) + 1)) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hy) hk.le
    _ = (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 * ‖DirichletCharacter.LFunction χ 1‖ := by ring

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelProductCharacterInequality
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem real_character_apply_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n.Coprime q) : χ (n : ZMod q) * χ (n : ZMod q) = 1 := by
  have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
  have h := congrArg (fun f : DirichletCharacter ℂ q => f (n : ZMod q)) hsq
  simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hu] at h
  rw [← sq]
  exact h

theorem product_real_characters_sq_eq_one {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h1 : χ₁ ^ 2 = 1) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) :
    ψ ^ 2 = 1 := by
  ext a
  have hm : (((a : ZMod (q₁ * q)).val : ℕ) : ZMod (q₁ * q)) = a := ZMod.natCast_zmod_val _
  set m := (a : ZMod (q₁ * q)).val with hmdef
  have hcop : m.Coprime (q₁ * q) :=
    (ZMod.isUnit_iff_coprime m (q₁ * q)).mp (by rw [hm]; exact a.isUnit)
  have c1 : m.Coprime q₁ := Nat.Coprime.coprime_dvd_right (dvd_mul_right q₁ q) hcop
  have c2 : m.Coprime q := Nat.Coprime.coprime_dvd_right (dvd_mul_left q q₁) hcop
  rw [MulChar.one_apply_coe, MulChar.pow_apply' ψ two_ne_zero, ← hm, hψ m, mul_pow,
    ← MulChar.pow_apply' χ₁ two_ne_zero, ← MulChar.pow_apply' χ two_ne_zero, h1, h2,
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m q₁).mpr c1),
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m q).mpr c2), one_mul]

theorem agree_coprime_of_product_principal {q₁ q : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) (hψ1 : ψ = 1) :
    ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q) := by
  intro n hn
  have hu : IsUnit (n : ZMod (q₁ * q)) := (ZMod.isUnit_iff_coprime n (q₁ * q)).mpr hn
  have e1 : χ₁ (n : ZMod q₁) * χ (n : ZMod q) = 1 := by
    rw [← hψ n, hψ1, MulChar.one_apply hu]
  have e2 := real_character_apply_sq_eq_one χ h2 (Nat.Coprime.coprime_dvd_right (dvd_mul_left q q₁) hn)
  calc χ₁ (n : ZMod q₁) = χ₁ (n : ZMod q₁) * (χ (n : ZMod q) * χ (n : ZMod q)) := by
        rw [e2, mul_one]
    _ = (χ₁ (n : ZMod q₁) * χ (n : ZMod q)) * χ (n : ZMod q) := by ring
    _ = χ (n : ZMod q) := by rw [e1, one_mul]

private theorem two_pow_card_primeFactors_le_self (n : ℕ) (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

private theorem card_primeFactors_add_one_sq_le_rpow {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : n ≠ 0) :
    ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ (2 / (ε * Real.log 2) + 1) ^ 2 * (n : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h2 : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast two_pow_card_primeFactors_le_self n hn
  have hcard : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hlog : Real.log n ≤ (n : ℝ) ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (by linarith) (by linarith)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < ε / 2)] at hlog
  have hR1 : 1 ≤ (n : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by linarith)
  have hc : (n.primeFactors.card : ℝ) ≤ 2 / (ε * Real.log 2) * (n : ℝ) ^ (ε / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hε hl2)]
    nlinarith [mul_le_mul_of_nonneg_right hcard (by linarith : (0 : ℝ) ≤ ε / 2)]
  have hb : (n.primeFactors.card : ℝ) + 1 ≤ (2 / (ε * Real.log 2) + 1) * (n : ℝ) ^ (ε / 2) := by
    nlinarith
  have h0 : 0 ≤ (n.primeFactors.card : ℝ) + 1 := by positivity
  calc ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ ((2 / (ε * Real.log 2) + 1) * (n : ℝ) ^ (ε / 2)) ^ 2 :=
        pow_le_pow_left₀ h0 hb 2
    _ = (2 / (ε * Real.log 2) + 1) ^ 2 * (n : ℝ) ^ ε := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (ε / 2)) 2, ← Real.rpow_mul (by positivity)]
        norm_num

private theorem div_le_mul_of_main_bound_caseA {σ ε C L₁ X Lψ Nk M Q Pc A : ℝ} (hε : 0 < ε) (h1σ : 0 < 1 - σ)
    (hL₁ : 0 < L₁) (hX : 0 ≤ X) (hA : 0 < A) (hNk0 : 0 ≤ Nk) (hLψ0 : 0 ≤ Lψ) (hM0 : 0 ≤ M)
    (hmain : (1 - σ) / 2 ≤ C * (L₁ * X * Lψ) * Nk) (hLψ : Lψ ≤ A * (M / (ε / 2))) (hNk : Nk ≤ M)
    (hMM : M * M = Pc * Q) (hPc : 0 < Pc) :
    (1 - σ) / (2 * max C 1 * L₁ * A * (2 / ε) * Pc) ≤ X * Q := by
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden : 0 < 2 * max C 1 * L₁ * A * (2 / ε) * Pc :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hCp) hL₁) hA) (div_pos two_pos hε)) hPc
  have hLX : 0 ≤ L₁ * X := mul_nonneg hL₁.le hX
  have hp : 0 ≤ L₁ * X * Lψ * Nk := mul_nonneg (mul_nonneg hLX hLψ0) hNk0
  have s1 : C * (L₁ * X * Lψ) * Nk ≤ max C 1 * (L₁ * X * Lψ * Nk) := by
    have := mul_le_mul_of_nonneg_right (le_max_left C 1) hp
    linarith
  have hAM : 0 ≤ A * (M / (ε / 2)) := mul_nonneg hA.le (div_nonneg hM0 (by linarith))
  have s2 : L₁ * X * Lψ * Nk ≤ L₁ * X * (A * (M / (ε / 2))) * M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hLψ hLX) hNk hNk0 (mul_nonneg hLX hAM)
  have s3 := mul_le_mul_of_nonneg_left s2 hCp.le
  have e : max C 1 * (L₁ * X * (A * (M / (ε / 2))) * M) =
      max C 1 * L₁ * A * (2 / ε) * X * (M * M) := by ring
  rw [hMM] at e
  rw [div_le_iff₀ hden]
  linarith

private theorem div_le_mul_of_chain_caseB {L₁ X W D Nε Pc Q : ℝ} (hL₁ : 0 < L₁) (hX : 0 ≤ X) (hD : 0 < D)
    (hPc : 0 < Pc) (hS : L₁ ≤ W * X) (hW : W ≤ D * Nε) (hN : Nε ≤ Pc * Q) :
    L₁ / (D * Pc) ≤ X * Q := by
  rw [div_le_iff₀ (mul_pos hD hPc)]
  calc L₁ ≤ W * X := hS
    _ ≤ D * Nε * X := mul_le_mul_of_nonneg_right hW hX
    _ ≤ D * (Pc * Q) * X := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hD.le) hX
    _ = X * Q * (D * Pc) := by ring

theorem siegel_product_character_inequality (hP : ProdCharExists) (hS : SameCharacterLFunctionOne) {C K CL : ℝ}
    (hKey : ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
      (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ₂ ψ →
      ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
        1 / 2 - C * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) ≤ (Fbq χ₁ χ₂ ψ σ).re)
    (hL : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ 1‖ ≤ CL * Real.log (3 * q))
    {ε : ℝ} (hε : 0 < ε) {q₁ : ℕ} [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁) (h1sq : χ₁ ^ 2 = 1)
    (h1ne : χ₁ ≠ 1) {σ : ℝ} (hσ78 : 7 / 8 ≤ σ) (hσ1 : σ < 1) (hKa : K * (1 - σ) ≤ ε / 2)
    (hneg : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ (q₁ * q)),
      χ ^ 2 = 1 → χ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ ψ → (Fbq χ₁ χ ψ σ).re ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
      c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  have h1σ : 0 < 1 - σ := by linarith
  have hL₁ : 0 < ‖DirichletCharacter.LFunction χ₁ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero h1ne)
  have hA : 0 < |CL| + 1 := by positivity
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hPc : 0 < ((3 : ℝ) * q₁) ^ ε := Real.rpow_pos_of_pos (by positivity) ε
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hD : 0 < (2 / (ε * Real.log 2) + 1) ^ 2 :=
    pow_pos (by have := div_pos two_pos (mul_pos hε hl2); linarith) 2
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hden : 0 < 2 * max C 1 * ‖DirichletCharacter.LFunction χ₁ 1‖ * (|CL| + 1) * (2 / ε) *
      ((3 : ℝ) * q₁) ^ ε :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hCp) hL₁) hA) (div_pos two_pos hε)) hPc
  refine ⟨min ((1 - σ) / (2 * max C 1 * ‖DirichletCharacter.LFunction χ₁ 1‖ * (|CL| + 1) * (2 / ε) *
      ((3 : ℝ) * q₁) ^ ε))
    (‖DirichletCharacter.LFunction χ₁ 1‖ / ((2 / (ε * Real.log 2) + 1) ^ 2 * ((3 : ℝ) * q₁) ^ ε)),
    lt_min (div_pos h1σ hden) (div_pos hL₁ (mul_pos hD hPc)), ?_⟩
  intro q _ χ hsq hne
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hQ : 0 < (q : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg hq0, ← div_eq_mul_inv, div_le_iff₀ hQ]
  have hN : ((q₁ * q : ℕ) : ℝ) = (q₁ : ℝ) * q := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q : ℕ) : ℝ) := by rw [hN]; nlinarith
  have hNε : ((q₁ * q : ℕ) : ℝ) ^ ε ≤ ((3 : ℝ) * q₁) ^ ε * (q : ℝ) ^ ε := by
    rw [hN, Real.mul_rpow (by linarith) hq0]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) hε.le) hQ.le
  obtain ⟨ψ, hψ⟩ := hP q₁ q χ₁ χ
  by_cases hψ1 : ψ = 1
  ·
    refine le_trans (min_le_right _ _) ?_
    exact div_le_mul_of_chain_caseB hL₁ (norm_nonneg _) hD hPc
      (hS q₁ q χ₁ χ h1ne hne (agree_coprime_of_product_principal χ₁ χ ψ hsq hψ hψ1))
      (card_primeFactors_add_one_sq_le_rpow hε (q₁ * q) (Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q))) hNε
  ·
    refine le_trans (min_le_left _ _) ?_
    have hk := hKey q₁ q χ₁ χ ψ h1sq hsq h1ne hne hψ1 hψ σ hσ78 hσ1
    have hn := hneg q χ ψ hsq hne hψ1 hψ
    have hmain : (1 - σ) / 2 ≤ C * (‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
        ‖DirichletCharacter.LFunction ψ 1‖) * ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) := by
      have h2 : 1 / 2 ≤ C * ‖lamBq χ₁ χ ψ‖ * ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) := by linarith
      rw [le_div_iff₀ h1σ] at h2
      have hlam : ‖lamBq χ₁ χ ψ‖ = ‖DirichletCharacter.LFunction χ₁ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
          ‖DirichletCharacter.LFunction ψ 1‖ := by simp only [lamBq, norm_mul]
      rw [hlam] at h2
      linarith
    have h3N : (1 : ℝ) ≤ 3 * ((q₁ * q : ℕ) : ℝ) := by linarith
    have hM0 : 0 ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) := by positivity
    have hlogb : Real.log (3 * ((q₁ * q : ℕ) : ℝ)) ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) / (ε / 2) :=
      Real.log_le_rpow_div (by linarith) (by linarith)
    have hLψ : ‖DirichletCharacter.LFunction ψ 1‖ ≤
        (|CL| + 1) * ((3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) / (ε / 2)) := by
      calc ‖DirichletCharacter.LFunction ψ 1‖ ≤ CL * Real.log (3 * ((q₁ * q : ℕ) : ℝ)) := hL (q₁ * q) ψ hψ1
        _ ≤ (|CL| + 1) * Real.log (3 * ((q₁ * q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self CL]) (Real.log_nonneg h3N)
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogb hA.le
    have hNk : ((q₁ * q : ℕ) : ℝ) ^ (K * (1 - σ)) ≤ (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) :=
      (Real.rpow_le_rpow_of_exponent_le hN1 hKa).trans
        (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
    have hMM : (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) * (3 * ((q₁ * q : ℕ) : ℝ)) ^ (ε / 2) =
        ((3 : ℝ) * q₁) ^ ε * (q : ℝ) ^ ε := by
      rw [← Real.rpow_add (by linarith), add_halves, hN, ← mul_assoc, Real.mul_rpow (by positivity) hq0]
    exact div_le_mul_of_main_bound_caseA hε h1σ hL₁ (norm_nonneg _) hA (by positivity) (norm_nonneg _) hM0
      hmain hLψ hNk hMM hPc

end Formalism.ZeroFreeDirichlet
end
end

