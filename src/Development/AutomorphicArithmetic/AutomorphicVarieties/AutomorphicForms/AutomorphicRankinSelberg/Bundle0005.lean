module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.OneLeNorm
section
open Set

namespace UpperTheory.V.Af.Rs

private lemma one_le_norm {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ ‖x i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (norm_le_pi_norm x i)

private lemma ker_le (hB : KerBd) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) {z : UpperHalfPlane}
    (hz : z ∈ ModularGroup.fd) (x : Fin 2 → ℤ) :
    ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
  obtain ⟨-, -, h3, -, -, h6⟩ := hB s hs
  have him0 : 0 < z.im := z.im_pos
  have him : 1 / 2 < z.im := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith
  by_cases hx : x = 0
  · subst hx
    rw [h3]
    simp
  · have hn := one_le_norm hx
    have hpos : 0 < ‖x‖ := by linarith
    have e1 : ‖x‖ ^ (-(2 * s)) ≤ ‖x‖ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith [hs.1])
    have e2 : ‖x‖ * ‖x‖ ^ (-3 : ℝ) = ‖x‖ ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have hp : 0 ≤ ‖x‖ ^ (-2 : ℝ) := Real.rpow_nonneg hpos.le _
    have hq : 4 * z.im ^ 2 ≤ 8 * z.im ^ 3 := by
      nlinarith [mul_pos (pow_pos him0 2) (by linarith : (0 : ℝ) < 2 * z.im - 1)]
    calc ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) := h6 x z hz
      _ ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-2 : ℝ) := by gcongr
      _ ≤ 8 * z.im ^ 3 * ‖x‖ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right hq hp
      _ = 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by rw [← e2]; ring

private lemma diff_le (hB : KerBd) (hD : KerDiff) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (1 : ℝ) 2,
    ∀ x x' : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
    |ker s x z - ker s x' z| ≤ C * ‖x - x'‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := hD
  refine ⟨max C 8, hC0.trans (le_max_left _ _), ?_⟩
  intro s hs x x' z hz
  obtain ⟨-, h2, h3, -⟩ := hB s hs
  have h0 : ‖(0 : Fin 2 → ℤ)‖ ^ (-3 : ℝ) = 0 := by
    rw [norm_zero]
    exact Real.zero_rpow (by norm_num)
  by_cases hx : x = 0
  · by_cases hx' : x' = 0
    · subst hx hx'
      rw [h3, sub_self, abs_zero]
      positivity
    · subst hx
      rw [h3, zero_sub, abs_neg, abs_of_nonneg (h2 _ _), zero_sub, norm_neg, h0, zero_add]
      calc ker s x' z ≤ 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := ker_le hB hs hz x'
        _ ≤ max C 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
  · by_cases hx' : x' = 0
    · subst hx'
      rw [h3, sub_zero, abs_of_nonneg (h2 _ _), sub_zero, h0, add_zero]
      calc ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := ker_le hB hs hz x
        _ ≤ max C 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
    · refine (hC s hs x x' hx hx' z hz).trans ?_
      gcongr
      exact le_max_left _ _

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.zDiff :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerDiff → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff := by
  intro hB hD hW L _
  obtain ⟨C, hC0, hC⟩ := diff_le hB hD
  have hS : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-3 : ℝ) := hW.1 3 (by norm_num)
  set S := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-3 : ℝ) with hSdef
  refine ⟨C * L * (2 * S), ?_⟩
  intro v v' s hs z hz
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h2, -, -, -, h6⟩ := hB s hs'
  have him : 0 < z.im := z.im_pos
  let a : Fin 2 → ℤ := fun i => ((v' i - v i : ZMod L).val : ℤ)
  have hcls : ∀ x, cls L (x + a) = v' ↔ cls L x = v := by
    intro x
    have e : cls L (x + a) = cls L x + (v' - v) := by
      funext i
      simp [cls, a, ZMod.natCast_zmod_val]
    rw [e]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  have ha : ‖a‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [a, Int.norm_eq_abs]
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    exact_mod_cast (ZMod.val_lt _).le
  have hker : Summable fun x : Fin 2 → ℤ => ker s x z := by
    refine Summable.of_nonneg_of_le (fun x => h2 x z) (fun x => h6 x z hz) ?_
    exact (hW.1 (2 * s) (by linarith [hs.1])).mul_left _
  have hker' : Summable fun x : Fin 2 → ℤ => ker s (x + a) z :=
    (Equiv.addRight a).summable_iff.mpr hker
  have hS' : Summable fun x : Fin 2 → ℤ => ‖x + a‖ ^ (-3 : ℝ) :=
    (Equiv.addRight a).summable_iff.mpr hS
  set g : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s x z else 0 with hg
  set g' : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s (x + a) z else 0 with hg'
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker
    · simp only [hg]
      split_ifs
      exacts [h2 x z, le_rfl]
    · simp only [hg]
      split_ifs
      exacts [le_rfl, h2 x z]
  have hgs' : Summable g' := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker'
    · simp only [hg']
      split_ifs
      exacts [h2 _ z, le_rfl]
    · simp only [hg']
      split_ifs
      exacts [le_rfl, h2 _ z]
  have hZ : Zc L v s z = ∑' x, g x := rfl
  have hZ' : Zc L v' s z = ∑' x, g' x := by
    show (∑' x, if cls L x = v' then ker s x z else 0) = _
    rw [← (Equiv.addRight a).tsum_eq (fun x => if cls L x = v' then ker s x z else 0)]
    congr 1
    funext x
    change (if cls L (x + a) = v' then ker s (x + a) z else 0) = g' x
    simp only [hg', hcls]
  have hd : ∀ x, |g x - g' x| ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
    intro x
    have hnn : 0 ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by positivity
    simp only [hg, hg']
    split_ifs
    · have e : ‖x - (x + a)‖ = ‖a‖ := by simp
      calc |ker s x z - ker s (x + a) z|
          ≤ C * ‖x - (x + a)‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
            hC s hs' x (x + a) z hz
        _ ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
            rw [e]
            gcongr
    · simpa using hnn
  have hh : Summable fun x : Fin 2 → ℤ =>
      C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
    (hS.add hS').mul_left _
  have hshift : ∑' x : Fin 2 → ℤ, ‖x + a‖ ^ (-3 : ℝ) = S :=
    (Equiv.addRight a).tsum_eq (fun x => ‖x‖ ^ (-3 : ℝ))
  have hsum : ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))
      = C * L * z.im ^ 3 * (2 * S) := by
    rw [tsum_mul_left, hS.tsum_add hS', hshift]
    ring
  rw [hZ, hZ', ← hgs.tsum_sub hgs']
  calc |∑' x, (g x - g' x)|
      ≤ ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
        rw [abs_le]
        constructor
        · rw [← tsum_neg]
          exact Summable.tsum_le_tsum (fun x => neg_le_of_abs_le (hd x)) hh.neg (hgs.sub hgs')
        · exact Summable.tsum_le_tsum (fun x => le_of_abs_le (hd x)) (hgs.sub hgs') hh
    _ = C * L * z.im ^ 3 * (2 * S) := hsum
    _ = C * L * (2 * S) * z.im ^ 3 := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.PetRe
section
open UpperHalfPlane hiding I
open UpperTheory.V.Af UpperTheory.V.Sd

private lemma pet_re (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    (petersson (k : ℤ) f f z).re = Complex.normSq (f z) * z.im ^ k := by
  simp only [petersson]
  rw [zpow_natCast, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sq_norm]

theorem UpperTheory.V.Af.Rs.core :
    UpperTheory.V.Af.Rs.TBdd → UpperTheory.V.Af.Rs.TTop → UpperTheory.V.Af.Rs.ClsEx → UpperTheory.V.Af.Rs.ClsProp → UpperTheory.V.Af.Rs.TEq → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.PetChar → UpperTheory.V.Af.Rs.Cmp → UpperTheory.V.Af.Rs.Core := by
  intro hTB hTT hCE hCP hTE hLB hNP hPC hCmp k L _ hk χ ψ g h hap hχ
  by_contra hne
  have hne' : χ * ψ⁻¹ ≠ 1 := fun e => hne (mul_inv_eq_one.mp e)
  obtain ⟨G, hG⟩ := hCE L (χ * ψ⁻¹) (petersson (k : ℤ) h.f g.f) (hPC k L χ ψ g.f h.f g.char h.char)
  have hNF := hNP k L g.f h.f
  obtain ⟨hP1, hP2, -⟩ := hCP L _ _ G hG
  obtain ⟨C, hC⟩ := hTB L G (hP1 hNF) (hP2 hne')
  have hchar0 := hPC k L χ χ g.f g.f g.char g.char
  simp only [mul_inv_cancel] at hchar0
  obtain ⟨G0, hG0⟩ := hCE L 1 (petersson (k : ℤ) g.f g.f) hchar0
  have hNF0 := hNP k L g.f g.f
  obtain ⟨hQ1, -, hQ3⟩ := hCP L _ _ G0 hG0
  have hfz : ∃ z, g.f z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : (⇑g.f : ℍ → ℂ) = 0 := funext hall
    have := g.one
    rw [h0] at this
    simp [UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨z0, hz0⟩ := hfz
  have hpos : ∃ z, 0 < (petersson (k : ℤ) g.f g.f z).re := by
    refine ⟨z0, ?_⟩
    rw [pet_re]
    exact mul_pos (Complex.normSq_pos.mpr hz0) (pow_pos z0.im_pos k)
  have hnn : ∀ z, 0 ≤ (petersson (k : ℤ) g.f g.f z).re := by
    intro z
    rw [pet_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le k)
  obtain ⟨hR1, hR2⟩ := hQ3 rfl hnn hpos
  obtain ⟨s, hs, hM⟩ := hTT L G0 (hQ1 hNF0) hR1 hR2 (56 * C + 1)
  have hs1 : (1 : ℝ) ≤ s := hs.1.le
  have e1 := hTE L _ _ G hG hNF (hP1 hNF) s hs
  have e0 := hTE L _ _ G0 hG0 hNF0 (hQ1 hNF0) s hs
  obtain ⟨-, hL1, -⟩ := hLB L (χ * ψ⁻¹) s hs1
  obtain ⟨-, -, hL0⟩ := hLB L 1 s hs1
  have hCs := hC s hs
  have hcmp := hCmp k L hk χ ψ g h hap hχ s hs
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e1, norm_mul, norm_mul, h2] at hCs
  have hre := Complex.re_le_norm (Rs.TT L G0 s)
  have hnorm : ‖Rs.TT L G0 s‖ = ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ *
      (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖) := by
    rw [e0, norm_mul, norm_mul, h2]
  have hA := norm_nonneg (Rs.stripI (petersson (k : ℤ) h.f g.f) s)
  have hB := norm_nonneg (Rs.stripI (petersson (k : ℤ) g.f g.f) s)
  have hX : ‖Rs.stripI (petersson (k : ℤ) h.f g.f) s‖ ≤ 2 * C := by nlinarith
  have hY : ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖)
      ≤ 2 * (2 * (7 * (2 * C))) := by
    apply mul_le_mul hL0 _ (by positivity) (by norm_num)
    linarith
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RankSum
section
open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private lemma UpperTheory.V.Af.Rs.upper_half_plane_point_im (x y : ℝ) (hy : 0 < y) : (UpperTheory.V.Af.Rs.pt x y).im = y := by
  unfold UpperTheory.V.Af.Rs.pt
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simp

theorem UpperTheory.V.Af.Rs.rankSum :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.MelSum → UpperTheory.V.Af.Rs.RankSum := by
  intro hFub hInt hNice hPars hMel k L _ f s hs
  have hs1 : 1 < s := hs.1
  have hI := hInt _ (hNice k L f f) s hs
  obtain ⟨hY, -⟩ := hFub _ hI
  have hPa := hPars k L f f
  have hPsum : ∀ y, 0 < y → HasSum (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y))
      ((∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re) := by
    intro y hy
    have h := Complex.reCLM.hasSum (hPa y hy)
    have e : (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y)) =
        fun n => Complex.reCLM (conj (coef f n) * coef f n * (Real.exp (-(4 * Real.pi * n) * y) : ℂ)) := by
      funext n
      rw [Complex.reCLM_apply, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [e]
    simpa only [Complex.reCLM_apply] using h
  have hY2 : IntegrableOn (fun y : ℝ => ((∫ x in (0 : ℝ)..1,
      UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) / ((y ^ 2 : ℝ) : ℂ)).re) (Ioi 0) := hY.re
  have hIntP : IntegrableOn (fun y : ℝ =>
      (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re *
        y ^ ((k : ℝ) + s - 1 - 1)) (Ioi 0) := by
    refine hY2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy' : 0 < y := hy
    have him : ∀ x, (UpperTheory.V.Af.Rs.pt x y).im = y := fun x => UpperTheory.V.Af.Rs.upper_half_plane_point_im x y hy'
    have hx : (∫ x in (0 : ℝ)..1, UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) =
        (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)) *
          ((y ^ k * y ^ s : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_mul_const]
      congr 1
      funext x
      simp [UpperHalfPlane.petersson, him, mul_assoc]
    dsimp only
    rw [hx, mul_div_assoc, ← Complex.ofReal_div, Complex.re_mul_ofReal]
    congr 1
    rw [show (k : ℝ) + s - 1 - 1 = ((k : ℝ) + s) - 2 by ring, Real.rpow_sub hy', Real.rpow_add hy',
      Real.rpow_natCast, Real.rpow_two]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact hMel (fun n => ‖coef f n‖ ^ 2) _ ((k : ℝ) + s - 1) (by linarith)
    (fun n => by positivity) hPsum hIntP
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Rankin
section
open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private theorem pt_im (x y : ℝ) (hy : 0 < y) : (pt x y).im = y := by
  simp [pt, UpperHalfPlane.ofComplex_apply_of_im_pos, hy]

private theorem coef_zero (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) : coef f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (by simp)

private theorem integrableOn_rpow_mul_exp_neg_Ioi (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ (A - 1) * Real.exp (-r * y)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A - 1) (b := r)
    (by linarith) one_pos hr
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

private theorem integral_rpow_mul_exp_neg_Ioi_eq_gamma_div (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    ∫ y in Ioi (0:ℝ), y ^ (A - 1) * Real.exp (-r * y) = Real.Gamma A / r ^ A := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hA hr
  simp only [neg_mul] at h ⊢
  rw [h, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
  ring

private theorem gamma_div_four_pi_mul_rpow_eq (A : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.Gamma A / (4 * Real.pi * n) ^ A = Real.Gamma A / (4 * Real.pi) ^ A / (n : ℝ) ^ A := by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (0:ℝ) < (4 * Real.pi) ^ A := by positivity
  have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
  field_simp

theorem UpperTheory.V.Af.Rs.rankin :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin := by
  intro hFub hInt hNice hPars hSum k L _ f g s hs
  have hs1 : 1 < s := hs.1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set A : ℝ := (k:ℝ) + s - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  set a : ℕ → ℂ := fun n => starRingEnd ℂ (coef g n) * coef f n with ha
  have ha0 : a 0 = 0 := by simp [ha, coef_zero k L f]
  set G : ℕ → ℝ → ℂ := fun n y =>
    a n * ((y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ) with hG
  have hpt : ∀ y : ℝ, 0 < y →
      (∫ x in (0:ℝ)..1, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ))
        / ((y ^ 2 : ℝ) : ℂ) = ∑' n, G n y := by
    intro y hy
    have h1 : ∀ x : ℝ, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ)
        = (starRingEnd ℂ (g (pt x y)) * f (pt x y)) * ((y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ)) := by
      intro x
      simp only [UpperHalfPlane.petersson, pt_im x y hy, zpow_natCast]
      ring
    have hyA : ((y ^ (A - 1) : ℝ) : ℂ) = (y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ) / ((y ^ 2 : ℝ) : ℂ) := by
      have hr : y ^ (A - 1) = y ^ k * y ^ s / y ^ 2 := by
        rw [show A - 1 = ((k:ℝ) + s) - 2 by rw [hAdef]; ring, Real.rpow_sub hy, Real.rpow_add hy,
          Real.rpow_natCast, Real.rpow_two]
      rw [hr]
      push_cast
      ring
    simp_rw [h1]
    rw [intervalIntegral.integral_mul_const, ← (hPars k L f g y hy).tsum_eq, ← tsum_mul_right,
      ← tsum_div_const]
    congr 1
    ext n
    simp only [hG, ha]
    rw [Complex.ofReal_mul, hyA]
    ring
  have hr : ∀ n : ℕ, 0 < n → (0:ℝ) < 4 * Real.pi * n := fun n hn => by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hGi : ∀ n, Integrable (G n) (volume.restrict (Ioi (0:ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : G 0 = fun _ => 0 := by funext y; simp [hG, ha0]
      rw [this]
      exact integrable_zero _ _ _
    · exact ((integrableOn_rpow_mul_exp_neg_Ioi A _ hA (hr n hn)).ofReal).const_mul (a n)
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n:ℝ) ^ A) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hSum k L f s hs).add (hSum k L g s hs)).div_const 2)
    have key : ‖coef g n‖ * ‖coef f n‖ ≤ (‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖coef f n‖ - ‖coef g n‖)]
    have hn : (0:ℝ) ≤ (n:ℝ) ^ A := by positivity
    calc ‖a n‖ / (n:ℝ) ^ A = (‖coef g n‖ * ‖coef f n‖) / (n:ℝ) ^ A := by
          simp [ha, norm_mul]
      _ ≤ ((‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2) / (n:ℝ) ^ A := by gcongr
      _ = _ := by ring
  have hGs : Summable (fun n => ∫ y in Ioi (0:ℝ), ‖G n y‖) := by
    refine (hsum.mul_left (Real.Gamma A / (4 * Real.pi) ^ A)).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hG, ha0]
    · have hc : ∫ y in Ioi (0:ℝ), ‖G n y‖
          = ∫ y in Ioi (0:ℝ), ‖a n‖ * (y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        have hy' : (0:ℝ) < y := hy
        simp only [hG, norm_mul, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [hc, integral_const_mul, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn]
      ring
  have hI := hInt _ (hNice k L f g) s hs
  obtain ⟨-, heq⟩ := hFub _ hI
  show (∫ z in strip, _) = _
  rw [heq, setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpt y hy),
    ← integral_tsum_of_summable_integral_norm hGi hGs, ← tsum_mul_left]
  congr 1
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hG, ha0, coef_zero k L f]
  · simp only [hG]
    rw [integral_const_mul, integral_complex_ofReal, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn, gam]
    have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
    push_cast
    field_simp
    simp only [ha]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowBij
section
open UpperHalfPlane hiding I
open scoped MatrixGroups

private theorem UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq {γ δ : SL(2, ℤ)}
    (h : UpperTheory.V.Af.Rs.row γ = UpperTheory.V.Af.Rs.row δ) : ∃ n : ℤ, γ = ModularGroup.T ^ n * δ := by
  have hc : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := congrFun h 0
  have hd : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := congrFun h 1
  have hγ := γ.det_coe
  have hδ := δ.det_coe
  rw [Matrix.det_fin_two] at hγ hδ
  refine ⟨-(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hδ
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hδ

private theorem UpperTheory.V.Af.Rs.row_T_zpow_mul (n : ℤ) (δ : SL(2, ℤ)) :
    UpperTheory.V.Af.Rs.row (ModularGroup.T ^ n * δ) = UpperTheory.V.Af.Rs.row δ := by
  funext i
  simp [UpperTheory.V.Af.Rs.row, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.V.Af.Rs.rowBij :
    UpperTheory.V.Af.Rs.RowBij := by
  refine ⟨fun γ => ModularGroup.bottom_row_coprime γ, ?_⟩
  intro z x
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ) (Set.mem_setOf_eq ▸ x.2 : x.1 ∈ _)
  have hrow : UpperTheory.V.Af.Rs.row g = x.1 := hg
  refine ⟨ModularGroup.T ^ (-⌊(g • z).re⌋) * g, ⟨?_, ?_⟩, ?_⟩
  · rw [UpperTheory.V.Af.Rs.row_T_zpow_mul, hrow]
  · show 0 ≤ (_ : ℍ).re ∧ (_ : ℍ).re < 1
    rw [mul_smul, ModularGroup.re_T_zpow_smul]
    push_cast
    constructor
    · linarith [Int.floor_le (g • z).re]
    · linarith [Int.lt_floor_add_one (g • z).re]
  · rintro γ' ⟨hr, hs⟩
    have hr' : UpperTheory.V.Af.Rs.row γ' = UpperTheory.V.Af.Rs.row g := by rw [hr, hrow]
    obtain ⟨m, rfl⟩ := UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq hr'
    have hs' : 0 ≤ ((ModularGroup.T ^ m * g) • z).re ∧ ((ModularGroup.T ^ m * g) • z).re < 1 := hs
    rw [mul_smul, ModularGroup.re_T_zpow_smul] at hs'
    have h1 : ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) < 1 := by
      push_cast
      linarith [Int.floor_le (g • z).re]
    have h2 : (-1 : ℝ) < ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.lt_floor_add_one (g • z).re]
    have h1' : m + ⌊(g • z).re⌋ < 1 := by exact_mod_cast h1
    have h2' : -1 < m + ⌊(g • z).re⌋ := by exact_mod_cast h2
    have hm : m = -⌊(g • z).re⌋ := by omega
    rw [hm]
end

