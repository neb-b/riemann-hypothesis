module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BRaabe
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_raabe :
    ∀ (N m k a : ℕ), 0 < N → 0 < m → bcoef N k a = ∑ j ∈ range m, bcoef (N * m) k (a + j * N) := by
  intro N m k a hN hm
  let F : ℕ → ℕ → PowerSeries ℚ := fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)
  let y : PowerSeries ℚ := PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)
  let E : PowerSeries ℚ := PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1
  have hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ) := by
    intro j
    simp only [y]
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  have hE : E = (∑ j ∈ range m, y ^ j) * (y - 1) := by
    rw [geom_sum_mul, hpow]
    simp only [E]
    push_cast
    rw [mul_comm (m : ℚ)]
  have hE0 : E ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1
    rcases h1 with h1 | h1
    · exact hN.ne' h1
    · exact hm.ne' h1
  suffices h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by
    have h2 := congrArg (PowerSeries.coeff k) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    simp only [F, PowerSeries.coeff_mk] at h2
    rw [← Finset.sum_div, div_left_inj' (by positivity)] at h2
    exact h2
  apply mul_right_cancel₀ hE0
  calc F N a * E = F N a * (y - 1) * ∑ j ∈ range m, y ^ j := by rw [hE]; ring
    _ = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) * ∑ j ∈ range m, y ^ j := by
        rw [b_egf N a hN]
    _ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
        push_cast
        rfl
    _ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]
    _ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUpper
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_upper :
    ∀ {N : ℕ} (k : ℕ) (Φ : ZMod N → ℂ), 0 < N → (∀ a, ‖Φ a‖ ≤ 1) → ‖genB k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro N k Φ hN hΦ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k with hC
  have hterm : ∀ a ∈ Icc 1 N,
      ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ ≤ (N : ℝ) ^ ((k : ℤ) - 1) * C := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hx0 : (0 : ℚ) ≤ (a : ℚ) / N := by positivity
    have hx1 : (a : ℚ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast ha.2
    have hb : ‖algebraMap ℚ ℂ (bcoef N k a)‖ =
        (N : ℝ) ^ ((k : ℤ) - 1) * |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, bcoef]
      push_cast
      rw [abs_mul, abs_of_pos (zpow_pos hNr _)]
    rw [norm_mul, hb]
    have hp := b_polybound k ((a : ℚ) / N) hx0 hx1
    calc ‖Φ (a : ZMod N)‖ * ((N : ℝ) ^ ((k : ℤ) - 1) *
          |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)|)
        ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * C) := by
          apply mul_le_mul (hΦ _) _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hp (zpow_pos hNr _).le
      _ = (N : ℝ) ^ ((k : ℤ) - 1) * C := one_mul _
  calc ‖genB k Φ‖ ≤ ∑ a ∈ Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * C := Finset.sum_le_sum hterm
    _ = 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          zpow_sub_one₀ hNr.ne', zpow_natCast, hC]
        field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denint
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_denint :
    ∀ (N k a : ℕ), 0 < N → ∃ z : ℤ, (den N k : ℚ) * bcoef N k a = z := by
  intro N k a hN
  suffices h : (den N k : ℚ) * bcoef N k a ∈ (Int.castRingHom ℚ).range by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz.symm⟩
  rw [b_expand N k a hN, Finset.mul_sum]
  refine Subring.sum_mem _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨z, hz⟩ := b_primden k j hjk
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : (N : ℚ) * (N : ℚ) ^ ((j : ℤ) - 1) = (N : ℚ) ^ j := by
    rw [← zpow_one_add₀ hN', add_sub_cancel, zpow_natCast]
  refine ⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩
  unfold den
  rw [eq_intCast]
  push_cast
  rw [← hz, ← hpow]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.FeLFunctionConstMul
section
open Finset UpperTheory.V.Bern

private lemma fe_LFunction_const_mul {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j => c * Φ j) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem UpperTheory.V.Bern.b_fe :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), χ.IsPrimitive → 1 ≤ k → χ (-1) = (-1) ^ k → ‖χ.LFunction (1 - k)‖ = 2 * ((k - 1).factorial : ℝ) * (N : ℝ) ^ ((k : ℝ) - 1 / 2) / (2 * Real.pi) ^ k * ‖χ⁻¹.LFunction k‖ := by
  intro N _ χ k hχ hk hpar
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set g := gaussSum χ ZMod.stdAddChar with hg
  have hinv1 : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg_one]
  have hF : ZMod.dft (χ : ZMod N → ℂ) = fun j => (χ (-1) * g) * χ⁻¹ j := by
    funext j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, show -j = -1 * j by ring, map_mul, hinv1]
    ring
  have hF' : ZMod.dft (fun x => χ (-x)) = fun j => g * χ⁻¹ j := by
    rw [ZMod.dft_comp_neg]
    funext j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]
    ring
  have hs : ∀ n : ℕ, ((m + 1 : ℕ) : ℂ) ≠ -n := by
    intro n h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hs' : χ 0 = 0 ∨ ((m + 1 : ℕ) : ℂ) ≠ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      apply χ.map_zero'
      rintro rfl
      have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [h1, map_one] at hpar
      norm_num at hpar
    · right
      exact_mod_cast (by omega : m + 1 ≠ 1)
  have hfe := ZMod.LFunction_one_sub (χ : ZMod N → ℂ) hs hs'
  rw [hF, hF', fe_LFunction_const_mul, fe_LFunction_const_mul] at hfe
  have he1 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = Complex.I ^ (m + 1) := by
    rw [show (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2
        = ((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  have he2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = (-Complex.I) ^ (m + 1) := by
    rw [show -(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2
        = ((m + 1 : ℕ) : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  have hGam : Complex.Gamma ((m + 1 : ℕ) : ℂ) = (m.factorial : ℂ) := by
    rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  have h2pi : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have key : ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ)) =
      (N : ℂ) ^ (((m + 1 : ℕ) : ℂ) - 1) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((m + 1 : ℕ) : ℂ)) *
        (m.factorial : ℂ) * g * ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) *
        (2 * (-Complex.I) ^ (m + 1)) := by
    rw [hfe, he1, he2, hGam, hpar, ← h2pi, neg_pow Complex.I]
    ring
  show ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ))‖ = _
  rw [key]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), (b_gauss χ hχ).1]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one, Complex.norm_natCast]
  have hre1 : (((m + 1 : ℕ) : ℂ) - 1).re = ((m : ℕ) : ℝ) := by simp
  have hre2 : (-((m + 1 : ℕ) : ℂ)).re = -((m + 1 : ℕ) : ℝ) := by simp
  have hL : DirichletCharacter.LFunction χ⁻¹ ((m + 1 : ℕ) : ℂ) = ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) := rfl
  have hNr : (N : ℝ) ^ (((m + 1 : ℕ) : ℝ) - 1 / 2) = (N : ℝ) ^ m * √(N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  rw [hre1, hre2, Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast, hL, hNr,
    Nat.add_sub_cancel, Complex.norm_two]
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (m + 1) := by positivity
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmap
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primmap :
    ∀ {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ (k : ℕ) (χ : DirichletCharacter R N), f (Bprim k χ) = Bprim k (χ.ringHomComp f) := by
  intro R S _ _ _ _ N _ f hf k χ
  obtain ⟨hcond, hval, -⟩ := b_condmap f hf χ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Bprim_eq, Bprim_eq, hcond, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, hval a, RingHom.map_rat_algebraMap]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Ratprod
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_ratprod :
    ∀ {N : ℕ} [NeZero N] (P : Set (Subgroup (ZMod N)ˣ)) (F : ∀ (Ω : Type) [Field Ω] [CharZero Ω], DirichletCharacter Ω N → Ω), (∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [CharZero Ω] (f : K →+* Ω) (χ : DirichletCharacter K N), f (F K χ) = F Ω (χ.ringHomComp f)) → ∃ q : ℚ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, F Ω χ = (q : Ω) := by
  intro N _ P F hF
  set e := Monoid.exponent (ZMod N)ˣ with he_def
  haveI he : NeZero e := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero (e : ℚ) := ⟨by exact_mod_cast he.out⟩
  haveI hcyc : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
    CyclotomicField.isCyclotomicExtension e ℚ
  haveI : IsGalois ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.isGalois {e} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField e ℚ) :=
    IsCyclotomicExtension.finiteDimensional {e} ℚ _
  have hζ := IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)
  haveI : HasEnoughRootsOfUnity (CyclotomicField e ℚ) e :=
    ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic (CyclotomicField e ℚ) e⟩
  have hfin : ∀ (Ω : Type) [Field Ω], (charSet Ω P).Finite := fun Ω _ => Set.toFinite _
  have hfix : ∀ σ : CyclotomicField e ℚ ≃ₐ[ℚ] CyclotomicField e ℚ,
      σ (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) =
        ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ := by
    intro σ
    have h1 := (σ.toRingHom.toMonoidHom).map_finprod_mem
      (fun χ => F (CyclotomicField e ℚ) χ) (hfin (CyclotomicField e ℚ))
    refine h1.trans ?_
    exact finprod_mem_eq_of_bijOn _ (b_charbij σ.toRingHom P)
      (fun χ _ => hF _ _ σ.toRingHom χ)
  have hbot := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hbot
  refine ⟨q, fun Ω _ _ _ => ?_⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω e
  have hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos e)), Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos e)
  let g := (hζ.powerBasis ℚ).lift ω hmin
  calc ∏ᶠ χ ∈ charSet Ω P, F Ω χ
      = ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, g.toRingHom (F (CyclotomicField e ℚ) χ) :=
        (finprod_mem_eq_of_bijOn _ (b_charbij g.toRingHom P)
          (fun χ _ => hF _ _ g.toRingHom χ)).symm
    _ = g.toRingHom (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) :=
        (g.toRingHom.toMonoidHom.map_finprod_mem _ (hfin _)).symm
    _ = (q : Ω) := by
        rw [← hq]
        exact g.commutes q |>.trans (eq_ratCast _ q)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termdiff
section
open Finset UpperTheory.V.Bern

private theorem termdiff_rpow_le {a e : ℝ} (ha : 0 < a) (h1 : -5 ≤ e) (h2 : e ≤ -(3 / 2)) :
    a ^ e ≤ 1 / |a| ^ (3 / 2 : ℝ) + 1 / |a| ^ (5 : ℝ) := by
  rw [abs_of_pos ha]
  have p1 : 0 ≤ 1 / a ^ (3 / 2 : ℝ) := by positivity
  have p2 : 0 ≤ 1 / a ^ (5 : ℝ) := by positivity
  rcases le_or_gt 1 a with h | h
  · have h' : a ^ e ≤ a ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le h h2
    rw [Real.rpow_neg ha.le, ← one_div] at h'
    linarith
  · have h' : a ^ e ≤ a ^ (-5 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha h.le h1
    rw [Real.rpow_neg ha.le, ← one_div] at h'
    linarith

private theorem termdiff_cpow {a : ℝ} (ha : 0 < a) : Differentiable ℂ (fun s : ℂ => (a : ℂ) ^ (-s)) := by
  exact Differentiable.const_cpow differentiable_id.neg (Or.inl (by exact_mod_cast ha.ne'))

theorem UpperTheory.V.Bern.b_termdiff :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))) ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) := by
  intro x hx0 hx1
  have hU : IsOpen ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => 24 * (1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ)))
    ?_ ?_ hU ?_
  · exact (((Real.summable_one_div_nat_add_rpow x (3 / 2)).2 (by norm_num)).add
      ((Real.summable_one_div_nat_add_rpow x 5).2 (by norm_num))).mul_left 24
  · intro n
    have hb : ∀ b : ℝ, 0 < b → Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (-s)) :=
      fun b hb => termdiff_cpow hb
    have h1 : (0 : ℝ) < (n : ℝ) + x := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact (((hb _ h1).sub (hb _ h2)).sub
      ((differentiable_const _).mul ((hb _ h2).sub (hb _ h3)))).differentiableOn
  · intro n s hs
    obtain ⟨hre, hball⟩ := hs
    simp only [Set.mem_setOf_eq] at hre
    rw [mem_ball_zero_iff] at hball
    have ha : (0 : ℝ) < (n : ℝ) + x := by positivity
    have hre2 : -2 ≤ s.re := by linarith
    have hR1 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + x) ha (by linarith) le_rfl hre2
    have hR2 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + 2) ha (by linarith) (by linarith) hre2
    have hA := termdiff_rpow_le ha (e := -s.re - 2)
      (by linarith [Complex.re_le_norm s]) (by linarith)
    have hA0 : 0 ≤ ((n : ℝ) + x) ^ (-s.re - 2) := Real.rpow_nonneg ha.le _
    have hs1 : ‖s + 1‖ ≤ 4 := by
      have := norm_add_le s 1
      rw [norm_one] at this
      linarith
    have hP : ‖s‖ * ‖s + 1‖ ≤ 3 * 4 := mul_le_mul hball.le hs1 (norm_nonneg _) (by norm_num)
    set B := 1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ) with hB
    have hB0 : 0 ≤ B := hA0.trans hA
    have hsq1 : ((n : ℝ) + x - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hsq2 : ((n : ℝ) + 2 - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hR1' := hR1.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq1 (sq_nonneg _) (by positivity))
    have hR2' := hR2.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq2 (sq_nonneg _) (by positivity))
    have hnx : ‖(1 : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ = ‖((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + x : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))
            + (1 - (x : ℂ)) * ((((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + 2 : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))‖ := by
          congr 1
          push_cast
          ring
      _ ≤ 3 * 4 * B * 1 + 1 * (3 * 4 * B * 1) :=
          (norm_add_le _ _).trans (by
            rw [norm_mul]
            exact add_le_add hR1' (mul_le_mul hnx hR2' (norm_nonneg _) zero_le_one))
      _ = 24 * B := by ring
end

