module

public import Formalism.HermitianCurvature.StatementJ

@[expose] public section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P.Jx1

theorem conv {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TB.PSDOn F k) :
    TA.PSDOn F (fun x y => k y x) := by
  unfold TB.PSDOn at h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  obtain ⟨hH, hN⟩ := h
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · have e := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
    simp only [Matrix.of_apply] at e
    show k x y = conj (k y x)
    rw [← e]
    simp
  · have hb := (Complex.le_def.mp (hN (fun i => conj (a i)))).1
    simp only [Complex.zero_re] at hb
    refine le_of_le_of_eq hb ?_
    congr 1
    rw [Finset.sum_comm, ← Finset.sum_coe_sort F]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring

private theorem im_quadratic_form_eq_zero_of_hermitian {α : Type} (F : Finset α) (k : α → α → ℂ)
    (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h

private theorem tb_psdOn_of_ta_psdOn {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) :
    TB.PSDOn F k := by
  classical
  unfold TB.PSDOn
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [h.1 i i.2 j j.2]
    simp
  · set a : α → ℂ := fun u => if hu : u ∈ F then x ⟨u, hu⟩ else 0 with ha
    have hQ : star x ⬝ᵥ (Matrix.of fun u v : F => k u v).mulVec x =
        ∑ u ∈ F, ∑ v ∈ F, conj (a u) * k u v * a v := by
      rw [← Finset.sum_coe_sort F]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ha, Complex.star_def, mul_assoc]
    rw [hQ, Complex.le_def]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨h.2 a, (im_quadratic_form_eq_zero_of_hermitian F k h.1 a).symm⟩

theorem t_PSDTranspose : PSDTranspose := by
  unfold PSDTranspose
  intro α F k h
  exact tb_psdOn_of_ta_psdOn F _ (conv F k h)

section Tower
variable {E : Type} [Field E]

end Tower

section Agree
variable {α : Type}

theorem q_im (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h

theorem ta_to_tb (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) : TB.PSDOn F k := by
  exact tb_psdOn_of_ta_psdOn F k h

theorem psd_form_conj_rewrite (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, conj ((fun z => conj (a z)) x) * k x y * (fun z => conj (a z)) y := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Complex.conj_conj]
  ring

theorem psd_kernel_hermitian (F : Finset α) (k : α → α → ℂ) (h : A5.IsPSD F k) :
    ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y) := by
  classical
  intro x hx y hy
  set B : (α → ℂ) → (α → ℂ) → ℂ := fun a b => ∑ u ∈ F, ∑ v ∈ F, a u * conj (b v) * k u v with hB
  have hS : ∀ a, (B a a).im = 0 := fun a => (h a).1
  have hexp : ∀ a b, B (a + b) (a + b) = B a a + B b b + (B a b + B b a) := by
    intro a b
    simp only [hB, Pi.add_apply, map_add (f := _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hpol : ∀ a b, (B a b + B b a).im = 0 := by
    intro a b
    have h0 := hS (a + b)
    rw [hexp, Complex.add_im, Complex.add_im, hS a, hS b] at h0
    simpa using h0
  have hsc1 : ∀ (c : ℂ) a b, B (c • a) b = c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hsc2 : ∀ (c : ℂ) a b, B a (c • b) = conj c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hBe : ∀ p q, p ∈ F → q ∈ F →
      B (fun u => if u = p then 1 else 0) (fun u => if u = q then 1 else 0) = k p q := by
    intro p q hp hq
    simp [hB, apply_ite (starRingEnd ℂ), ite_mul, hp, hq]
  have h1 := hpol (fun u => if u = x then 1 else 0) (fun u => if u = y then 1 else 0)
  have h2 := hpol (fun u => if u = x then 1 else 0) (Complex.I • fun u => if u = y then 1 else 0)
  rw [hsc2, hsc1] at h2
  rw [hBe x y hx hy, hBe y x hy hx] at h1 h2
  apply Complex.ext <;> simp [Complex.mul_im] at h1 h2 ⊢ <;> linarith

theorem t_PSDAgree : PSDAgree := by
  unfold PSDAgree
  intro α F k
  refine ⟨⟨fun h => conv F _ (t_PSDTranspose α F k h), ta_to_tb F k⟩, ⟨fun h => ⟨psd_kernel_hermitian F k h, fun a => ?_⟩, fun h => ?_⟩⟩
  · have h2 := (h (fun z => conj (a z))).2
    refine le_of_le_of_eq h2 ?_
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Complex.conj_conj]
    ring
  · intro a
    rw [psd_form_conj_rewrite F k a]
    exact ⟨q_im F k h.1 _, h.2 _⟩

end Agree

theorem t_BoxSumLattice : BoxSumLattice := by
  classical
  unfold BoxSumLattice
  intro hB
  unfold Formalism.SA.C.BoxSum at hB
  obtain ⟨C₀, hC₀⟩ := hB
  refine ⟨max 1 |C₀|, le_max_left _ _, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hΘpos : 0 < Θ := by linarith
  have hapos : 0 < a := by linarith
  have hd0 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
  have wnn : ∀ (w : InfinitePlace E) (l : E), 0 ≤ w l := by
    intro w l
    first
    | positivity
    | exact w.nonneg l
    | exact apply_nonneg w l
  have hNq : (0 : ℝ) < (FractionalIdeal.absNorm aa : ℝ) := by
    first
    | (have h1 : FractionalIdeal.absNorm aa ≠ 0 := by
         simpa [FractionalIdeal.absNorm_eq_zero_iff] using haa
       have h2 : (0 : ℚ) ≤ FractionalIdeal.absNorm aa := FractionalIdeal.absNorm_nonneg aa
       exact_mod_cast lt_of_le_of_ne h2 (Ne.symm h1))
    | exact_mod_cast FractionalIdeal.absNorm_pos_iff.mpr haa
  have hNpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) := Real.sqrt_pos.mpr hNq
  set T : ℝ := (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) with hT
  have hTpos : 0 < T := mul_pos (pow_pos (div_pos hapos hΘpos) _) hNpos
  obtain ⟨y, hxy, hy0, hyT⟩ : ∃ y : InfinitePlace E → ℝ, (∀ w, x w ≤ y w) ∧ (∀ w, 0 < y w) ∧
      ∏ w, y w ≤ T := by
    by_cases hpos : ∀ w, 0 < x w
    · exact ⟨x, fun _ => le_rfl, hpos, hprod⟩
    · push_neg at hpos
      obtain ⟨w₀, hw₀⟩ := hpos
      have hxw0 : x w₀ = 0 := le_antisymm hw₀ (hx w₀)
      set M : ℝ := 1 + ∑ w, x w with hM
      have hsum0 : 0 ≤ ∑ w, x w := Finset.sum_nonneg fun w _ => hx w
      have hM1 : 1 ≤ M := by linarith
      have hMpos : 0 < M := by linarith
      set ε : ℝ := min 1 (T / M ^ Fintype.card (InfinitePlace E)) with hε
      have hεpos : 0 < ε := lt_min one_pos (div_pos hTpos (pow_pos hMpos _))
      refine ⟨fun w => max (x w) ε, fun w => le_max_left _ _,
        fun w => lt_of_lt_of_le hεpos (le_max_right _ _), ?_⟩
      have hcomp : ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε ≤
          M ^ Fintype.card (InfinitePlace E) := by
        calc ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε
            ≤ ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), M := by
              apply Finset.prod_le_prod₀ (fun w _ => le_trans hεpos.le (le_max_right _ _))
              intro w _
              apply max_le
              · have h3 : x w ≤ ∑ v, x v := Finset.single_le_sum (fun v _ => hx v) (Finset.mem_univ w)
                linarith
              · exact le_trans (min_le_left _ _) hM1
          _ = M ^ ({w₀}ᶜ : Finset (InfinitePlace E)).card := Finset.prod_const M
          _ ≤ M ^ Fintype.card (InfinitePlace E) := pow_le_pow_right₀ hM1 (Finset.card_le_univ _)
      show ∏ w, max (x w) ε ≤ T
      rw [Fintype.prod_eq_mul_prod_compl w₀, hxw0, max_eq_right hεpos.le]
      calc ε * ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε
          ≤ ε * M ^ Fintype.card (InfinitePlace E) := mul_le_mul_of_nonneg_left hcomp hεpos.le
        _ ≤ (T / M ^ Fintype.card (InfinitePlace E)) * M ^ Fintype.card (InfinitePlace E) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos hMpos _).le
        _ = T := div_mul_cancel₀ T (pow_pos hMpos _).ne'
  have hPpos : 0 < ∏ w, y w := Finset.prod_pos fun w _ => hy0 w
  have hQpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w := div_pos hNpos hPpos
  set Θ' : ℝ := (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w) ^ ((1 : ℝ) / Fintype.card (InfinitePlace E))
    with hΘ'
  have hΘ'nn : 0 ≤ Θ' := Real.rpow_nonneg hQpos.le _
  have hΘ'd : Θ' ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w := by
    rw [hΘ', ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
    have hdr : ((1 : ℝ) / Fintype.card (InfinitePlace E)) * (Fintype.card (InfinitePlace E) : ℝ) = 1 := by
      field_simp
    rw [hdr, Real.rpow_one]
  have hΘ'ge : Θ / a ≤ Θ' := by
    have h1 : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ' ^ Fintype.card (InfinitePlace E) := by
      rw [hΘ'd, le_div_iff₀ hPpos]
      calc (Θ / a) ^ Fintype.card (InfinitePlace E) * ∏ w, y w
          ≤ (Θ / a) ^ Fintype.card (InfinitePlace E) * T :=
            mul_le_mul_of_nonneg_left hyT (pow_pos (div_pos hΘpos hapos) _).le
        _ = √(FractionalIdeal.absNorm aa : ℝ) := by
            rw [hT, ← mul_assoc, ← mul_pow]
            have hone : Θ / a * (a / Θ) = 1 := by field_simp
            rw [hone, one_pow, one_mul]
    first
    | exact le_of_pow_le_pow_left₀ hd0.ne' hΘ'nn h1
    | exact (pow_le_pow_iff_left₀ (div_pos hΘpos hapos).le hΘ'nn hd0.ne').mp h1
  have hΘ'2 : 2 < Θ' := lt_of_lt_of_le (by rw [lt_div_iff₀ hapos]; linarith) hΘ'ge
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hbox := hC₀ E aa haa y Θ' (K : ℝ) hy0 hΘ'2 hK3 hΘ'd
  unfold TA.LatSum
  constructor
  · intro l
    unfold prof
    exact Finset.prod_nonneg fun w _ => le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (wnn w l)) _)
  · intro S hS
    have hS' : ∀ l ∈ S, l ∈ aa ∧ l ≠ 0 := fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩
    have h1 := hbox S hS'
    have hs : 0 < (K : ℝ) - 5 / 2 := by linarith
    have ht0 : 0 ≤ Θ' ^ (-((K : ℝ) - 5 / 2)) := Real.rpow_nonneg hΘ'nn _
    have htle : Θ' ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      have hta : 0 < Θ / a := div_pos hΘpos hapos
      rw [Real.rpow_neg hΘ'nn, Real.rpow_neg hΘpos.le]
      have h2 : (Θ / a) ^ ((K : ℝ) - 5 / 2) ≤ Θ' ^ ((K : ℝ) - 5 / 2) :=
        Real.rpow_le_rpow hta.le hΘ'ge hs.le
      have h3 : (Θ' ^ ((K : ℝ) - 5 / 2))⁻¹ ≤ ((Θ / a) ^ ((K : ℝ) - 5 / 2))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hta _) h2
      refine le_trans h3 (le_of_eq ?_)
      rw [Real.div_rpow hΘpos.le hapos.le, inv_div, div_eq_mul_inv]
    calc ∑ l ∈ S, prof x K l ≤ ∑ l ∈ S, ∏ w, min 1 ((y w / w l) ^ (K : ℝ)) := by
          apply Finset.sum_le_sum
          intro l _
          unfold prof
          apply Finset.prod_le_prod₀
          · intro w _
            exact le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (wnn w l)) _)
          · intro w _
            rw [Real.rpow_natCast]
            apply min_le_min_left
            exact pow_le_pow_left₀ (div_nonneg (hx w) (wnn w l)) (div_le_div_of_nonneg_right (hxy w) (wnn w l)) _
      _ ≤ (C₀ * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := h1
      _ ≤ (|C₀| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := by
          have e : (|C₀| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) =
              |(C₀ * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)| := by
            rw [abs_pow, abs_mul, abs_of_nonneg ht0]
          rw [e]
          exact le_abs_self _
      _ ≤ (max 1 |C₀| * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := by
          apply pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) ht0)
          rw [mul_assoc]
          exact mul_le_mul (le_max_right _ _) htle ht0 (le_trans zero_le_one (le_max_left _ _))

end Formalism.FourierDecayAlt.P.Jx1

namespace Formalism.FourierDecayAlt.P

theorem psd_agree : Formalism.FourierDecayAlt.J.PSDAgree := Jx1.t_PSDAgree

theorem box_sum_lattice : Formalism.FourierDecayAlt.J.BoxSumLattice := Jx1.t_BoxSumLattice

end Formalism.FourierDecayAlt.P
