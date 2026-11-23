module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0003
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0001
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0002
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0003

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqEntire
section
open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def zetaSubPole : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

theorem zeta_sub_pole_differentiable : Differentiable ℂ zetaSubPole := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hev : zetaSubPole =ᶠ[𝓝 s] fun z => riemannZeta z - 1 / (z - 1) := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
      exact Function.update_of_ne hz _ _
    have hd : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s :=
      (differentiableAt_riemannZeta hs1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · unfold zetaSubPole
    exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

theorem zeta_minus_pole_eq {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaSubPole
  exact Function.update_of_ne hs _ _

theorem dirichlet_product_entire : BqEntire := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h₁ h₂ hψ
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => DirichletCharacter.LFunction χ₁ s *
      DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction ψ s := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]
    exact ((DirichletCharacter.differentiable_LFunction h₁).mul
      (DirichletCharacter.differentiable_LFunction h₂)).mul
      (DirichletCharacter.differentiable_LFunction hψ)
  have hds : Differentiable ℂ (dslope P 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hPd.differentiableOn
  refine ⟨fun s => zetaSubPole s * P s + dslope P 1 s,
    (zeta_sub_pole_differentiable.mul hPd).add hds, fun s hs => ?_⟩
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  show _ = zetaSubPole s * P s + dslope P 1 s + _
  rw [dslope_of_ne _ hs, slope_def_field, zeta_minus_pole_eq hs]
  simp only [Fbq, lamBq, hP]
  field_simp
  ring

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqGrowth
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma circle_about_two_geometry {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) :
    1 / 2 ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ 1 / 2 ≤ ‖s - 1‖ := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Complex.abs_re_le_norm (s - 2)
    rw [hs] at h
    have e : (s - 2).re = s.re - 2 := by simp
    rw [e] at h
    linarith [(abs_le.mp h).1]
  · have h := norm_add_le (s - 2) (2 : ℂ)
    rw [sub_add_cancel, hs] at h
    have e : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  · have h := norm_add_le (s - 1) (-1 : ℂ)
    have e : s - 1 + -1 = s - 2 := by ring
    rw [e, hs] at h
    have e1 : ‖(-1 : ℂ)‖ = 1 := by simp
    linarith

lemma zeta_norm_le_on_circle {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) : ‖riemannZeta s‖ ≤ 14 := by
  obtain ⟨hre, hn, h1⟩ := circle_about_two_geometry hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    norm_num at h1
  have hg := Formalism.ZF.growthBound s (by linarith) hs1
  have ha : 1 / ‖s - 1‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hb : 1 / s.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hp : 0 ≤ 1 + 1 / s.re := by
    have : 0 < 1 / s.re := by apply div_pos <;> linarith
    linarith
  have hc : ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * 3 := by
    calc ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * (1 + 1 / s.re) := mul_le_mul_of_nonneg_right hn hp
      _ ≤ 7 / 2 * 3 := by linarith
  linarith

theorem product_lfunction_growth_bound : BqGrowth := by
  obtain ⟨C, hC⟩ := lfunction_polynomial_growth
  refine ⟨14 * (9 / 2 * |C|) ^ 3, 3, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h3 s hs
  obtain ⟨hre, hn, -⟩ := circle_about_two_geometry hs
  have hz := zeta_norm_le_on_circle hs
  have L : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ 9 / 2 * |C| * q := by
    intro q _ χ hχ
    have h := hC q χ hχ s hre
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hCq : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq
    have hp : 0 ≤ |C| * q := by positivity
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖) := h
      _ ≤ |C| * q * (1 + ‖s‖) := mul_le_mul_of_nonneg_right hCq (by positivity)
      _ ≤ |C| * q * (9 / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
      _ = 9 / 2 * |C| * q := by ring
  have e1 := L q₁ χ₁ h1
  have e2 := L q₂ χ₂ h2
  have e3 := L (q₁ * q₂) ψ h3
  have hq1 : (q₁ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right q₁ (Nat.pos_of_ne_zero (NeZero.ne q₂))
  have hq2 : (q₂ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left q₂ (Nat.pos_of_ne_zero (NeZero.ne q₁))
  have ha : 0 ≤ 9 / 2 * |C| := by positivity
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold Fbq
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ₁ s‖ * ‖DirichletCharacter.LFunction χ₂ s‖ *
        ‖DirichletCharacter.LFunction ψ s‖
      ≤ 14 * (9 / 2 * |C| * q₁) * (9 / 2 * |C| * q₂) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by
        gcongr
    _ ≤ 14 * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) *
          (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by gcongr
    _ = 14 * (9 / 2 * |C|) ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 3 := by ring

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.CharExists
section
open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet

theorem isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by
  intro n
  rw [MulChar.mul_apply]
  by_cases h : IsUnit (n : ZMod (q₁ * q₂))
  · have h1 : ∀ {q : ℕ} (hq : q ∣ q₁ * q₂) (χ : DirichletCharacter ℂ q),
        DirichletCharacter.changeLevel hq χ (n : ZMod (q₁ * q₂)) = χ (n : ZMod q) := by
      intro q hq χ
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ := χ) hq h.unit
      rw [IsUnit.unit_spec] at this
      rw [this]
      congr 1
      first
        | exact ZMod.cast_natCast hq n
        | exact ZMod.cast_natCast hq _ n
        | exact ZMod.cast_nat_cast hq n
    rw [h1, h1]
  · rw [MulChar.map_nonunit _ h]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right] at h
    rcases not_and_or.mp h with h' | h'
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime])]
      simp
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime])]
      simp

theorem exists_product_character : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩

def characterModFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

theorem characterModFour_sq : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem characterModFour_ne_one : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3

theorem exists_real_nontrivial_character : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ConvolutionNonnegOfDivisors
section
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma convolution_nonneg_of_divisors (f g : ArithmeticFunction ℂ) (n : ℕ)
    (hf : ∀ d, d ∣ n → 0 ≤ f d) (hg : ∀ d, d ∣ n → 0 ≤ g d) : 0 ≤ (f * g) n := by
  change 0 ≤ ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2
  refine Finset.sum_nonneg fun x hx => ?_
  have h := (Nat.mem_divisorsAntidiagonal.1 hx).1
  exact mul_nonneg (hf _ (Dvd.intro _ h)) (hg _ (Dvd.intro_left _ h))

lemma character_convolution_eq {N N' M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ N')
    (ψ : DirichletCharacter ℂ M) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    (n : ℕ) :
    (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M))) n
      = χ' (n : ZMod N') * DirichletCharacter.zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) a *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)) b), DirichletCharacter.zetaMul,
    coe_zeta_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hni : n / i ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hi0)).ne'
  simp only [toArithmeticFunction, coe_mk, hi0, hni, if_false]
  rw [hψ i]
  calc χ' ((n / i : ℕ) : ZMod N') * (χ (i : ZMod N) * χ' (i : ZMod N'))
      = (χ' ((n / i : ℕ) : ZMod N') * χ' (i : ZMod N')) * χ (i : ZMod N) := by ring
    _ = χ' (n : ZMod N') * χ (i : ZMod N) := by
      rw [← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]


set_option backward.isDefEq.respectTransparency.types false in
lemma prime_power_coefficient_nonneg {N N' M : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {ψ : DirichletCharacter ℂ M} (hχ : χ ^ 2 = 1) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    {p : ℕ} (hp : p.Prime)
    (hc : χ' (p : ZMod N') = 0 ∨ χ' (p : ZMod N') = 1 ∨ (χ' (p : ZMod N') = -1 ∧ χ (p : ZMod N) = -1))
    (k : ℕ) :
    0 ≤ (DirichletCharacter.zetaMul χ * (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)))) (p ^ k) := by
  have hζ : ∀ j, DirichletCharacter.zetaMul χ (p ^ j) = ∑ i ∈ Finset.range (j + 1), χ (p : ZMod N) ^ i := by
    intro j
    rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [toArithmeticFunction, hp.ne_zero]
  apply convolution_nonneg_of_divisors
  · intro d _
    exact DirichletCharacter.zetaMul_nonneg hχ d
  · intro d hd
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [character_convolution_eq χ χ' ψ hψ, Nat.cast_pow, map_pow]
    rcases hc with h | h | ⟨h, h'⟩
    · exact mul_nonneg (by rw [h]; exact pow_nonneg le_rfl j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · exact mul_nonneg (by rw [h]; exact pow_nonneg zero_le_one j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · rw [h, hζ, h', neg_one_geom_sum]
      split_ifs with he
      · simp
      · have hj : Even j := by
          rcases Nat.even_or_odd j with hj | hj
          · exact hj
          · exact absurd hj.add_one he
        rw [hj.neg_one_pow]
        norm_num

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsContourAvoidingRealZero
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem exists_contour_avoiding_real_zero (B : Finset ℝ) (hB : B.card ≤ 1) (L c₁ : ℝ) (hL : 0 < L) (hc₁ : 0 < c₁) :
    ∃ σ₁ : ℝ, (σ₁ = 1 - c₁ / (3 * L) ∨ σ₁ = 1 - c₁ / (4 * L)) ∧
      ∀ β ∈ B, c₁ / (24 * L) ≤ |σ₁ - β| := by
  have hab : (1 - c₁ / (3 * L)) - (1 - c₁ / (4 * L)) = -(2 * (c₁ / (24 * L))) := by
    field_simp
    ring
  have he : 0 < c₁ / (24 * L) := by positivity
  rcases Finset.eq_empty_or_nonempty B with hB0 | ⟨β, hβ⟩
  · exact ⟨_, Or.inl rfl, fun β hβ => by simp [hB0] at hβ⟩
  have hBs : ∀ β' ∈ B, β' = β := fun β' hβ' => Finset.card_le_one.mp hB β' hβ' β hβ
  by_cases h : c₁ / (24 * L) ≤ |(1 - c₁ / (3 * L)) - β|
  · exact ⟨_, Or.inl rfl, fun β' hβ' => by rw [hBs β' hβ']; exact h⟩
  · refine ⟨_, Or.inr rfl, fun β' hβ' => ?_⟩
    rw [hBs β' hβ']
    push_neg at h
    have tri := abs_sub_le (1 - c₁ / (3 * L)) β (1 - c₁ / (4 * L))
    rw [hab, abs_neg, abs_of_pos (by positivity), abs_sub_comm β] at tri
    linarith

theorem perron_contour_decomposition (hP : PerronChi) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y σ₁ σ₀ T : ℝ) (R : ℂ) (hy : 1 ≤ y) (hσ₀ : 1 < σ₀) (hT : 0 ≤ T)
    (hrect : Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T) T = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Schi χ y - R‖ ≤
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I)‖
      + ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ := by
  obtain ⟨hint, hS⟩ := hP q χ y hy σ₀ hσ₀
  have hsplit := integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint
  have hIoc : ∫ t in Set.Ioc (-T) T, Fchi χ y ((σ₀ : ℂ) + t * I) =
      ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  unfold Formalism.ZF.rectInt at hrect
  set Cp := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I) with hCp
  set Bt := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt
  set Tp := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I) with hTp
  set Lf := ∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I) with hLf
  set Rt := ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) with hRt
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hinv : (2 * (Real.pi : ℂ)) * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hI : I * I = -1 := Complex.I_mul_I
  have key : (2 * (Real.pi : ℂ)) * (Schi χ y - R) = Cp + I * (Bt - Tp) + Lf := by
    rw [hS, ← hsplit, hIoc]
    linear_combination (-I) * hrect + (Rt + Cp) * hinv + (Rt - Lf - 2 * Real.pi * R) * hI
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hsub := norm_sub_le Bt Tp
  calc 2 * Real.pi * ‖Schi χ y - R‖ = ‖(2 * (Real.pi : ℂ)) * (Schi χ y - R)‖ := by
        rw [norm_mul, hn]
    _ = ‖Cp + I * (Bt - Tp) + Lf‖ := by rw [key]
    _ ≤ ‖Cp‖ + ‖I * (Bt - Tp)‖ + ‖Lf‖ := norm_add₃_le
    _ ≤ ‖Cp‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.IteratedDerivInvSubOneAtTwo
section
open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma iteratedDeriv_inv_sub_one_at_two (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by
  have h : (fun s : ℂ => (s - 1)⁻¹) = fun x => (1 * x - 1)⁻¹ := by simp
  rw [iteratedDeriv_eq_iterate, h, iter_deriv_inv_linear_sub]
  norm_num

lemma iteratedDeriv_lseries_at_two {a : ℕ → ℂ} {G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hFG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹) (m : ℕ) :
    iteratedDeriv m (LSeries a) 2 = iteratedDeriv m G 2 + lam * ((-1) ^ m * (m ! : ℂ)) := by
  have hU : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : LSeries a =ᶠ[nhds (2 : ℂ)] fun s => G s + lam * (s - 1)⁻¹ := by
    filter_upwards [hU] with s hs using hFG s hs
  have hinv : ContDiffAt ℂ m (fun s : ℂ => lam * (s - 1)⁻¹) 2 :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))
  rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_fun_add hG.contDiff.contDiffAt hinv,
    iteratedDeriv_const_mul_field, iteratedDeriv_inv_sub_one_at_two]

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRealPos
section
open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma real_character_lfunction_im_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (σ : ℝ) : (DirichletCharacter.LFunction χ σ).im = 0 := by
  have h := realCharConj q χ hχ hχ1 (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.1 h.symm

lemma lfunction_tendsto_one_atTop {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun x : ℝ ↦ DirichletCharacter.LFunction χ x) atTop (𝓝 1) := by
  have ha : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne q) χ]
    exact EReal.coe_lt_top 1
  have ht := LSeries.tendsto_atTop ha
  simp only [Nat.cast_one, map_one] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hx)).symm

theorem real_lfunction_real_on_reals : LRealPos := by
  intro q _ χ hχ hχ1 σ₀ hnz σ hσ
  have him : ∀ t : ℝ, (DirichletCharacter.LFunction χ t).im = 0 := real_character_lfunction_im_eq_zero χ hχ hχ1
  refine ⟨him σ, ?_⟩
  by_contra hneg
  rw [not_lt] at hneg
  have hcont : Continuous fun t : ℝ => (DirichletCharacter.LFunction χ t).re :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp Complex.continuous_ofReal)
  obtain ⟨x, hx1, hx⟩ : ∃ x : ℝ, σ ≤ x ∧ 0 < (DirichletCharacter.LFunction χ x).re := by
    have hev : ∀ᶠ x : ℝ in atTop, 0 < (DirichletCharacter.LFunction χ x).re :=
      ((Complex.continuous_re.tendsto 1).comp (lfunction_tendsto_one_atTop χ)).eventually
        (lt_mem_nhds (by norm_num))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop σ)).exists
    exact ⟨x, hx.2, hx.1⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx1 hcont.continuousOn ⟨hneg, hx.le⟩
  apply hnz c (le_trans hσ hc.1)
  exact Complex.ext (by simpa using hc0) (by simpa using him c)

end Formalism.ZeroFreeDirichlet
end
end

