module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.DvdOfModEq
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

section Series

variable {K : Type} [Field K] [CharZero K]

end Series

section Root

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

end Root

end UpperTheory.Kd.L

private theorem eps_eOm_eq_cexp {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) := by
  unfold eOm
  apply Function.invFun_eq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have h2 := hξ.map_of_injective ε.injective
  have h1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    linear_combination (2 * ↑Real.pi * Complex.I) * hx
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one h1
  exact ⟨ξ ^ i, by rw [map_pow, hi]⟩

private theorem eOm_inv_mul_pow_eq_eOm_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M : ℕ) (hD : 0 < D) :
    eOm ε (1 / ((D * M : ℕ) : ℚ)) ^ D = eOm ε (1 / (M : ℚ)) := by
  apply ε.injective
  rw [map_pow, eps_eOm_eq_cexp, eps_eOm_eq_cexp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  have : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  by_cases hM : (M:ℂ) = 0
  · simp [hM]
  · field_simp

private theorem eisF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (n : ℕ) :
    eisF 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then eisF 1 M ζ A a (n / D) else 0 := by
  have hD' : (D:ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x : ℤ, x ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] → (D:ℤ) ∣ x := by
    intro x hx
    have h := hx.symm.dvd
    push_cast at h
    have h2 : (D:ℤ) ∣ x - D * A := (Dvd.intro _ rfl).trans h
    have h3 : (D:ℤ) ∣ D * A := Dvd.intro _ rfl
    simpa using h2.add h3
  have cong : ∀ y : ℤ, (((D:ℤ) * y) ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] ↔ y ≡ A [ZMOD M]) := by
    intro y
    push_cast
    exact ⟨Int.ModEq.mul_left_cancel' hD', fun h => Int.ModEq.mul_left' h⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [eisF, const0, if_true, dvd_zero, Nat.zero_div]
    have h1 : ¬ ((D * M : ℕ) : ℤ) ∣ (D:ℤ) * A := by
      push_cast
      rwa [mul_dvd_mul_iff_left hD']
    rw [if_neg h1, if_neg hA]
    unfold frc
    push_cast
    rw [Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hD)]
    push_cast
    have : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · simp only [eisF, coefPos, hn.ne', if_false, Nat.sub_self, pow_zero, one_mul]
    by_cases hDn : D ∣ n
    · rw [if_pos hDn]
      obtain ⟨k, rfl⟩ := hDn
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hn
      rw [Nat.mul_div_cancel_left k hD, if_neg hk]
      have hsub : k.divisors ⊆ (D * k).divisors :=
        Nat.divisors_subset_of_dvd (Nat.mul_ne_zero hD.ne' hk) (dvd_mul_left k D)
      have hpow : ∀ t : ℤ, ζ' ^ ((D:ℤ) * t) = ζ ^ t := by
        intro t
        rw [zpow_mul, zpow_natCast, hζ]
      have hout : ∀ x : ℕ, x ∣ D * k → (D:ℤ) ∣ ((D * k / x : ℕ) : ℤ) → x ∣ k := by
        intro x hx hdx
        rw [Int.natCast_dvd_natCast] at hdx
        obtain ⟨e, he⟩ := hdx
        have h1 : D * k / x * x = D * k := Nat.div_mul_cancel hx
        rw [he, mul_assoc] at h1
        exact ⟨e, by rw [mul_comm x e]; exact (Nat.eq_of_mul_eq_mul_left hD h1).symm⟩
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro x hx
        have hxk : x ∣ k := Nat.dvd_of_mem_divisors hx
        have e1 : ((D * k / x : ℕ) : ℤ) = (D:ℤ) * ((k / x : ℕ) : ℤ) := by
          rw [Nat.mul_div_assoc D hxk]
          push_cast
          ring
        simp only [e1, neg_mul_eq_mul_neg, cong, mul_assoc, hpow]
      · intro x hx hxn
        have hx' : x ∣ D * k := Nat.dvd_of_mem_divisors hx
        have hnot : ¬ x ∣ k := fun h => hxn (Nat.mem_divisors.mpr ⟨h, hk⟩)
        rw [if_neg, if_neg, sub_zero]
        · intro h
          exact hnot (hout x hx' (by simpa using key _ h))
        · intro h
          exact hnot (hout x hx' (key _ h))
    · rw [if_neg hDn]
      apply Finset.sum_eq_zero
      intro x hx
      have hx' : x ∣ n := Nat.dvd_of_mem_divisors hx
      have hout : (D:ℤ) ∣ ((n / x : ℕ) : ℤ) → False := by
        intro hdx
        rw [Int.natCast_dvd_natCast] at hdx
        exact hDn (hdx.trans (Nat.div_dvd_of_dvd hx'))
      rw [if_neg, if_neg, sub_zero]
      · intro h
        exact hout (by simpa using key _ h)
      · intro h
        exact hout (key _ h)

private theorem smF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (c : ℤ) (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (hcA : ¬ (M:ℤ) ∣ c * A) (n : ℕ) :
    smF c 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then smF c 1 M ζ A a (n / D) else 0 := by
  unfold smF
  rw [mul_left_comm c (D:ℤ) A, mul_left_comm c (D:ℤ) a, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ A a hD hA, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ (c * A) (c * a) hD hcA]
  split_ifs <;> simp

private theorem cmul_dilate_eq_ite_dvd {K : Type*} [Field K] (D : ℕ) (hD : 0 < D) (f g f' g' : ℕ → K) (hf : ∀ n, f' n = if D ∣ n then f (n / D) else 0) (hg : ∀ n, g' n = if D ∣ n then g (n / D) else 0) (N : ℕ) :
    cmul f' g' N = if D ∣ N then cmul f g (N / D) else 0 := by
  unfold cmul
  by_cases hN : D ∣ N
  · rw [if_pos hN]
    obtain ⟨K0, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left K0 hD]
    have hsub : (Finset.range (K0 + 1)).image (fun k => D * k) ⊆ Finset.range (D * K0 + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
      obtain ⟨k, hk, rfl⟩ := hi
      have := Nat.mul_le_mul_left D (Nat.lt_succ_iff.mp hk)
      omega
    rw [← Finset.sum_subset hsub, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      have e : D * K0 - D * k = D * (K0 - k) := (Nat.mul_sub D K0 k).symm
      rw [hf, hg, if_pos (dvd_mul_right D k), e, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD, Nat.mul_div_cancel_left _ hD]
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hD hxy
    · intro i hi hni
      rw [hf]
      split_ifs with hDi
      · exfalso
        obtain ⟨k, rfl⟩ := hDi
        apply hni
        simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
        refine ⟨k, ?_, rfl⟩
        have h1 : D * k ≤ D * K0 := by omega
        have := Nat.le_of_mul_le_mul_left h1 hD
        omega
      · simp
  · rw [if_neg hN]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hf, hg]
    split_ifs with h1 h2
    · exfalso
      apply hN
      have := Nat.dvd_add h1 h2
      rwa [Nat.add_sub_cancel' hi'] at this
    · simp
    · simp
    · simp

private theorem coefQ_eq_of_mul_eq_nat {Ω : Type} [Field Ω] (L : ℕ) (hL : 0 < L) (F : ℕ → Ω) (r : ℚ) (N : ℕ) (h : r * L = N) :
    coefQ L F r = F N := by
  unfold coefQ
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  have hr : 0 ≤ r := by
    have h0 : 0 ≤ r * L := by
      rw [h]
      exact Nat.cast_nonneg _
    exact (mul_nonneg_iff_of_pos_right hL').mp h0
  rw [if_pos ⟨hr, by rw [h]; simp⟩, h]
  simp

private theorem coefQ_eq_zero_of_not_nat {Ω : Type} [Field Ω] (L : ℕ) (F : ℕ → Ω) (r : ℚ) (h : ¬ ∃ N : ℕ, r * L = N) :
    coefQ L F r = 0 := by
  unfold coefQ
  rw [if_neg]
  rintro ⟨hr, hd⟩
  apply h
  have h1 : ((r * L).num : ℚ) = r * L := Rat.coe_int_num_of_den_eq_one hd
  have h2 : 0 ≤ (r * L).num := Rat.num_nonneg.mpr (mul_nonneg hr (Nat.cast_nonneg _))
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h2
  refine ⟨m, ?_⟩
  rw [← h1, hm]
  simp

theorem UpperTheory.Kd.L.resc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M c d L : ℕ) (A a B b : ℤ), 0 < D → 0 < M → 0 < L → ¬ (M : ℤ) ∣ A → ¬ (M : ℤ) ∣ c * A → ¬ (M : ℤ) ∣ B → ¬ (M : ℤ) ∣ d * B → ∀ r : ℚ, coefQ L (cmul (smF c 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * A) (D * a)) (smF d 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * B) (D * b))) r = coefQ L (cmul (smF c 1 M (eOm ε (1 / (M : ℚ))) A a) (smF d 1 M (eOm ε (1 / (M : ℚ))) B b)) (r / D) := by
  intro Ω _ _ _ _ ε D M c d L A a B b hD hM hL hA hcA hB hdB r
  have hζ := eOm_inv_mul_pow_eq_eOm_inv ε D M hD
  have h1 := smF_mul_scale_eq_ite_dvd (c:ℤ) D M _ _ hζ A a hD hA hcA
  have h2 := smF_mul_scale_eq_ite_dvd (d:ℤ) D M _ _ hζ B b hD hB hdB
  have hc := cmul_dilate_eq_ite_dvd D hD _ _ _ _ h1 h2
  by_cases h : ∃ N : ℕ, r * L = N
  · obtain ⟨N, hN⟩ := h
    rw [coefQ_eq_of_mul_eq_nat L hL _ r N hN, hc]
    by_cases hDN : D ∣ N
    · obtain ⟨K0, rfl⟩ := hDN
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD]
      refine (coefQ_eq_of_mul_eq_nat L hL _ _ K0 ?_).symm
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      rw [div_mul_eq_mul_div, hN]
      push_cast
      field_simp
    · rw [if_neg hDN, coefQ_eq_zero_of_not_nat]
      rintro ⟨m, hm⟩
      apply hDN
      refine ⟨m, ?_⟩
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      have e : (N:ℚ) = D * m := by
        rw [← hN, ← hm]
        field_simp
      exact_mod_cast e
  · rw [coefQ_eq_zero_of_not_nat L _ r h, coefQ_eq_zero_of_not_nat]
    rintro ⟨m, hm⟩
    apply h
    refine ⟨D * m, ?_⟩
    have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    rw [← hm]
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsAdmissibleSmoothingFactorAddIntVector
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.AdmissibleUnits

open GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem ent_ext {g h : GQ} (e : ∀ i j, ent g i j = ent h i j) : g = h :=
  Subtype.ext (Matrix.GeneralLinearGroup.ext e)

private theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ent_dg {N : ℕ} (hN : 0 < N) (i j : Fin 2) :
    ent (toGQ !![(N : ℤ), 0; 0, 1]) i j = (!![(N : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j := by
  fin_cases i <;> fin_cases j <;> simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem ent_sl (γ : SL(2, ℤ)) (i j : Fin 2) : ent (ofSL γ) i j = (en γ i j : ℚ) := rfl

private theorem dg_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    toGQ !![(a : ℤ), 0; 0, 1] * toGQ !![(b : ℤ), 0; 0, 1] = toGQ !![((a * b : ℕ) : ℤ), 0; 0, 1] := by
  refine ent_ext fun i j => ?_
  rw [ent_mul, ent_dg (Nat.mul_pos ha hb)]
  simp only [ent_dg ha, ent_dg hb]
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_conj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) :
    ∃ δ : SL(2, ℤ), en δ 0 0 = en γ 0 0 ∧ en δ 0 1 = N * en γ 0 1 ∧ en δ 1 0 = k ∧ en δ 1 1 = en γ 1 1 ∧
      toGQ !![(N : ℤ), 0; 0, 1] * ofSL γ = ofSL δ * toGQ !![(N : ℤ), 0; 0, 1] := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  let δ : SL(2, ℤ) := ⟨!![en γ 0 0, N * en γ 0 1; k, en γ 1 1], by
    rw [Matrix.det_fin_two_of, ← hd, hk]; ring⟩
  have h00 : en δ 0 0 = en γ 0 0 := rfl
  have h01 : en δ 0 1 = N * en γ 0 1 := rfl
  have h10 : en δ 1 0 = k := rfl
  have h11 : en δ 1 1 = en γ 1 1 := rfl
  refine ⟨δ, h00, h01, h10, h11, ent_ext fun i j => ?_⟩
  rw [ent_mul, ent_mul]
  simp only [ent_dg hN, ent_sl]
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hk, mul_comm]

private theorem admissible_of_integral_conj_le {c D : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcD : Nat.Coprime c D) (hD : 0 < D) {a b : ℤ}
    (hab : ¬ ((D : ℤ) ∣ a ∧ (D : ℤ) ∣ b)) : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D] := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : IsCoprime (D : ℤ) (c : ℤ) := Nat.isCoprime_iff_coprime.2 hcD.symm
  have key : ∀ z : ℤ, (c : ℚ) * ((z : ℚ) / D) ∈ Set.range ((↑) : ℤ → ℚ) → (D : ℤ) ∣ z := by
    rintro z ⟨k, hk⟩
    have e : (c : ℚ) * z = D * k := by rw [hk]; field_simp
    exact hz.dvd_of_dvd_mul_left ⟨k, by exact_mod_cast e⟩
  exact ⟨hc, h6, fun h => hab ⟨key a h.1, key b h.2⟩⟩

private theorem siegel_per {ε : Ω →+* ℂ} (X : Tower Ω ε) {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : siegel X c y = siegel X c x := by
  have hy : y = fun i => x i + ((![p, q] : Fin 2 → ℤ) i : ℚ) := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have e : sgC c y = sgC c x := by
    funext z
    rw [hy]
    exact _root_.GlobalTheory.Sieg.Per.sg_add_int c x _ _ hx
  unfold siegel
  rw [e]

private theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : GlobalTheory.Sieg.admitted c y := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ => hx.2.2 ⟨⟨u - c * p, ?_⟩, ⟨v - c * q, ?_⟩⟩⟩
  · push_cast; rw [hu, h0]; ring
  · push_cast; rw [hv, h1]; ring

private theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hq : (en γ 0 0 : ℚ) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by exact_mod_cast hd
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ =>
    hx.2.2 ⟨⟨u * en γ 1 1 - v * en γ 1 0, ?_⟩, ⟨v * en γ 0 0 - u * en γ 0 1, ?_⟩⟩⟩
  all_goals
    simp only [act, Fin.sum_univ_two] at hu hv
    simp only [en] at hq ⊢
    push_cast
    rw [hu, hv]
  · linear_combination (c * x 0) * hq
  · linear_combination (c * x 1) * hq

private theorem sl_dg_siegel [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N : ℕ} (hN : 0 < N) {x y : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) (p q : ℤ)
    (h0 : y 0 = x 0 * en γ 0 0 + x 1 * k + p) (h1 : y 1 = x 0 * (N * en γ 0 1) + x 1 * en γ 1 1 + q) :
    X.sl (ofSL γ) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c x)) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c y) := by
  obtain ⟨δ, h00, h01, h10, h11, e⟩ := exists_conj hN γ k hk
  rw [← X.sl_mul, e, X.sl_mul, _root_.GlobalTheory.KZ.SiegelSL.sl_siegel Ω ε X c x δ hx]
  congr 1
  simp only [en] at h00 h01 h10 h11 h0 h1
  refine (siegel_per X (admissible_act_SL2 hx δ) p q ?_ ?_).symm
  · simp only [act, Fin.sum_univ_two]; rw [h0, h00, h10]
  · simp only [act, Fin.sum_univ_two]; rw [h1, h01, h11]; push_cast; ring

private theorem gal_siegel_fix [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c D : ℕ} (hD : 0 < D) {a b : ℤ}
    (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ z : Ω, z ^ D = 1 → s z = z) :
    X.gal s (siegel X c ![(a : ℚ) / D, (b : ℚ) / D]) = siegel X c ![(a : ℚ) / D, (b : ℚ) / D] := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨a', ha'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hz)
  obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hz)
  have hlt : a' < D := by
    have := Int.emod_lt_of_pos a (by exact_mod_cast hD : (0 : ℤ) < D)
    omega
  have ea : (a : ℚ) = a' + D * ((a / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv a D
    rw [ha'] at this
    exact_mod_cast this.symm
  have eb : (b : ℚ) = b' + D * ((b / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv b D
    rw [hb'] at this
    exact_mod_cast this.symm
  have f0 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 0 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 0 + ((-(a / D) : ℤ) : ℚ) := by
    show (a' : ℚ) / D = (a : ℚ) / D + ((-(a / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -ea
  have f1 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 1 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 1 + ((-(b / D) : ℤ) : ℚ) := by
    show (b' : ℚ) / D = (b : ℚ) / D + ((-(b / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -eb
  have hy := isAdmissibleSmoothingFactor_add_intVector hx _ _ f0 f1
  rw [← siegel_per X hx _ _ f0 f1]
  have := _root_.GlobalTheory.KZ.gal_siegel Ω ε X c D a' b' 1 s hD hlt
    (by rw [Nat.cast_one]; exact hs _ (isPrimitiveRoot_eOm ε hD.ne').pow_eq_one) hy (by rwa [one_mul])
  rwa [one_mul] at this

private theorem gal_dg {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) {f : X.K} (hf : X.gal s f = f) :
    X.gal s (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f := by
  apply X.exp.toRingHom.injective
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, GlobalTheory.DlRescale.exp_sl_diag ε X N hN, GlobalTheory.DlRescale.resc_coeff, ← X.gal_exp, hf]

private theorem sgN_mem [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N D M : ℕ} (hN : 0 < N) (hD : 0 < D)
    (hM : N * D ∣ M) {a b : ℤ} (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) :
    sgN X c N D (a, b) ∈ topF X M ∧ sgN X c N D (a, b) ≠ 0 := by
  refine ⟨(mem_mdl_iff X _ _ _).2 ⟨?_, fun s hs => ?_⟩, ?_⟩
  · rw [mem_lev_iff]
    intro γ hγ
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have hMz : ((N * D : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.2 hM
    obtain ⟨u, hu⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 0 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h00))
    obtain ⟨v, hv⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 1 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h01)
    obtain ⟨w, hw⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 0 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h10)
    obtain ⟨t, ht⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 1 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h11))
    have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    refine sl_dg_siegel X hN hx γ (D * w) (by rw [hw]; push_cast; ring) (-(a * N * u + b * w)) (-(a * N * N * v + b * N * t)) ?_ ?_
    · show (a : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 hu]; push_cast; field_simp; ring
    · show (b : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 ht, hv]; push_cast; field_simp; ring
  · refine gal_dg X hN s (gal_siegel_fix X hD hx s fun z hz => (mem_fixMu_iff s).1 hs z ?_)
    obtain ⟨e, rfl⟩ := (Dvd.intro_left N rfl : D ∣ N * D).trans hM
    rw [pow_mul, hz, one_pow]
  · exact (map_ne_zero _).2 (_root_.GlobalTheory.KZ.siegel_ne_zero Ω ε X c _ hx)

end UpperTheory.Kd.L.AdmissibleUnits

open UpperTheory.Kd.L.AdmissibleUnits in
theorem UpperTheory.Kd.L.units :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ((sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ∈ topF X (topMu l n m N) ∧ (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ≠ 0 ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ∈ topF X (topMu l n m N) ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ≠ 0) ∧ ∀ g ∈ CongruenceSubgroup.Gamma0 N, X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) = sgN X c (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n))), (N : ℤ) ^ 2 * ((N : ℤ) ^ 2 * en g 0 1)) ∧ X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) = sgN X d (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) + en g 1 0), (N : ℤ) ^ 2 * ((N : ℤ) * en g 1 1)) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm P x m n hm
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hL : 0 < l ^ (m + n) := pow_pos hl _
  have hD : 0 < N * l ^ (m + n) := Nat.mul_pos hN hL
  have hlL : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
  have cop : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 ∧ Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    ⟨he.coprime_mul_right_right.coprime_mul_right_right,
      Nat.Coprime.mul_right he.coprime_mul_left_right
        (Nat.Coprime.pow_right _ he.coprime_mul_right_right.coprime_mul_left_right)⟩
  have hlD : (l : ℤ) ∣ ((N * l ^ (m + n) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (hlL.mul_left N)
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => P.cop (Int.natCast_dvd_natCast.1 h)
  have hM : N * (N * l ^ (m + n)) ∣ topMu l n m N := ⟨1, by unfold topMu; ring⟩
  generalize (topT l (m + n) N : ℤ) = t
  have hu := admissible_of_integral_conj_le P.c1 (cop c P.cc).1 (cop c P.cc).2 hD
    (a := (N : ℤ) + (x.val : ℤ) * t * (l : ℤ) ^ (m + n)) (b := 0) (fun h => hlN
      ((dvd_add_left ((dvd_pow_self (l : ℤ) (by omega)).mul_left _)).1 (hlD.trans h.1)))
  have hv := admissible_of_integral_conj_le P.d1 (cop d P.dc).1 (cop d P.dc).2 hD
    (a := t * (l : ℤ) ^ (m + n)) (b := (N : ℤ)) (fun h => by
      have h2 := Nat.le_of_dvd hN (Int.natCast_dvd_natCast.1 h.2)
      have h3 : 1 < l ^ (m + n) := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
      nlinarith)
  refine ⟨⟨(sgN_mem X hN hD hM hu).1, (sgN_mem X hN hD hM hu).2, (sgN_mem X hN hD hM hv).1, (sgN_mem X hN hD hM hv).2⟩,
    fun g hg => ?_⟩
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ en g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 hg)
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have e3 : N * (N * N) = N ^ 3 := by ring
  unfold sgN
  constructor
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hu g k hk 0 (-(x.val * t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hv g k hk 0 (-(t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hk]; push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
end

