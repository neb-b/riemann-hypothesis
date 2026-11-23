module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BOneSum
section
open Finset UpperTheory.V.Bern

private theorem UpperTheory.V.Bern.b_one_sum {R : Type} [AddCommMonoid R] {N : ℕ} [NeZero N] (Φ : ZMod N → R) :
    ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = ∑ a : ZMod N, Φ a := by
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun b => (b - 1).val + 1) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro b _
    simp only [Finset.mem_Icc]
    exact ⟨by omega, ZMod.val_lt _⟩
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    have hk : k < N := by omega
    simp [Nat.cast_add, ZMod.val_cast_of_lt hk]
  · intro b _
    push_cast
    simp
  · intro a _
    rfl

theorem UpperTheory.V.Bern.b_one :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (Φ : ZMod N → R), ∑ a : ZMod N, Φ a = 0 → (N : R) * genB 1 Φ = ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * (a : R) := by
  intro R _ _ N _ Φ hΦ
  simp only [genB, bcoef, Polynomial.bernoulli_one]
  have hs : ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = 0 := (UpperTheory.V.Bern.b_one_sum Φ).trans hΦ
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ x : ℕ, (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) = Φ (x : ZMod N) * (x : R) - algebraMap ℚ R ((N : ℚ) / 2) * Φ (x : ZMod N) := by
    intro x
    have e : (N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)) = (x : ℚ) - (N : ℚ) / 2 := by
      simp
      field_simp
    calc (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)))
        = Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) := by
          rw [map_mul (algebraMap ℚ R) (N : ℚ), map_natCast]
          ring
      _ = _ := by
          rw [e, map_sub, map_natCast]
          ring
  rw [Finset.mul_sum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BTaylor2
section
open Finset UpperTheory.V.Bern

private lemma hd_cpow (c : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hmem : ((t : ℂ)) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 ht
  exact (Complex.hasStrictDerivAt_cpow_const (c := c) hmem).hasDerivAt.comp_ofReal

private lemma lip (s : ℂ) (a x y : ℝ) (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) (hs : -2 ≤ s.re) :
    ‖(y : ℂ) ^ (-s - 1) - (x : ℂ) ^ (-s - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) * ‖y - x‖ := by
  have hge : ∀ z ∈ Set.uIcc x y, a ≤ z := by
    intro z hz
    rcases Set.mem_uIcc.1 hz with h | h
    · exact le_trans hx h.1
    · exact le_trans hy h.1
  have hder : ∀ z ∈ Set.uIcc x y, HasDerivWithinAt (fun w : ℝ => (w : ℂ) ^ (-s - 1))
      ((-s - 1) * (z : ℂ) ^ (-s - 1 - 1)) (Set.uIcc x y) z := by
    intro z hz
    exact (hd_cpow (-s - 1) z (lt_of_lt_of_le ha (hge z hz))).hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc x y, ‖(-s - 1) * (z : ℂ) ^ (-s - 1 - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0]
    have h1 : ‖-s - 1‖ = ‖s + 1‖ := by
      rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    have h2 : (-s - 1 - 1).re = -s.re - 2 := by
      simp; ring
    rw [h1, h2]
    have h3 : z ^ (-s.re - 2) ≤ a ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos ha (hge z hz) (show -s.re - 2 ≤ 0 by linarith)
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc x y)
    Set.left_mem_uIcc Set.right_mem_uIcc

theorem UpperTheory.V.Bern.b_taylor2 :
    ∀ (s : ℂ) (a u v : ℝ), 0 < a → a ≤ u → a ≤ v → -2 ≤ s.re → ‖(v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
  intro s a u v ha hu hv hs
  have hge : ∀ z ∈ Set.uIcc u v, a ≤ z := by
    intro z hz
    rcases Set.mem_uIcc.1 hz with h | h
    · exact le_trans hu h.1
    · exact le_trans hv h.1
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1) with hg
  have hder : ∀ z ∈ Set.uIcc u v, HasDerivWithinAt g
      (-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)) (Set.uIcc u v) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    have h1 := hd_cpow (-s) z hz0
    have h2 : HasDerivAt (fun x : ℝ => s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1))
        (s * 1 * (u : ℂ) ^ (-s - 1)) z :=
      (((hasDerivAt_id z).ofReal_comp.sub_const (u : ℂ)).const_mul s).mul_const _
    have h3 := (h1.sub_const ((u : ℂ) ^ (-s))).add h2
    simp only [mul_one] at h3
    exact h3.hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc u v, ‖-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)‖ ≤
      ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by
    intro z hz
    have he : -s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1) =
        s * ((u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)) := by ring
    rw [he, norm_mul]
    have hl := lip s a z u ha (hge z hz) hu hs
    have hd : ‖u - z‖ ≤ ‖v - u‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
      exact Set.abs_sub_left_of_mem_uIcc hz
    have hC : 0 ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by positivity
    calc ‖s‖ * ‖(u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖u - z‖) := by gcongr
      _ ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by ring
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc u v)
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hgu : g u = 0 := by simp [hg]
  have hgv : g v = (v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1) := rfl
  rw [hgu, sub_zero, hgv] at key
  calc _ ≤ _ := key
    _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
      rw [Real.norm_eq_abs, mul_assoc _ |v - u| |v - u|, ← sq, sq_abs]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUltraUnit
section
open Finset UpperTheory.V.Bern

private theorem b_ultra_int {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {y : Ω}
    (h : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Ω)).integer y := h.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Ω))).mem_of_integral h1
  have h3 : ‖y‖₊ ≤ 1 := h2
  exact_mod_cast h3

private theorem b_ultra_unit {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) :
    ‖(m : Ω)‖ = 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).mpr hm
  have h1 : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlt : ‖(l : Ω)‖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ hl1
  refine le_antisymm (IsUltrametricDist.norm_intCast_le_one Ω m) ?_
  by_contra hc
  push Not at hc
  have ha := IsUltrametricDist.norm_intCast_le_one Ω a
  have hb := IsUltrametricDist.norm_intCast_le_one Ω b
  have h2 := IsUltrametricDist.norm_add_le_max ((a : Ω) * l) ((b : Ω) * m)
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have h3 : ‖(a : Ω)‖ * ‖(l : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha (norm_nonneg _) hlt
  have h4 : ‖(b : Ω)‖ * ‖(m : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) hc
  exact absurd h2 (not_le.mpr (max_lt h3 h4))

private theorem b_ultra_log {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (M : ℤ) (hM : M ≠ 0) :
    -Real.log ‖(M : Ω)‖ = (padicValInt l M : ℝ) * Real.log l := by
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := l) M
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have : (l : ℤ) ^ (padicValInt l M + 1) ∣ M := ⟨c, by
      conv_lhs => rw [hm, hc]
      ring⟩
    rcases (padicValInt_dvd_iff _ _).mp this with h | h
    · exact hM h
    · omega
  have h1 : (M : Ω) = (l : Ω) ^ padicValInt l M * m := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hm
  rw [h1, norm_mul, b_ultra_unit l hn m hnd, mul_one, norm_pow, hn, Real.log_pow, Real.log_inv]
  ring

theorem UpperTheory.V.Bern.b_ultra :
    ∀ {Ω ι : Type} [NormedField Ω] [IsUltrametricDist Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime], ‖(l : Ω)‖ = (l : ℝ)⁻¹ → ∀ (S : Set ι) (x : ι → Ω) (D : ℕ) (M : ℤ), S.Finite → M ≠ 0 → (∀ i ∈ S, IsIntegral ℤ ((D : Ω) * x i)) → ∏ᶠ i ∈ S, (D : Ω) * x i = (M : Ω) → ∑ᶠ i ∈ S, max 0 (-Real.log ‖x i‖) ≤ (padicValInt l M : ℝ) * Real.log l := by
  intro Ω ι _ _ _ l _ hn S x D M hS hM hint hprod
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at hprod
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← b_ultra_log l hn M hM, ← hprod, norm_prod]
  have hM' : (M : Ω) ≠ 0 := by exact_mod_cast hM
  have hne : ∀ i ∈ hS.toFinset, (D : Ω) * x i ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hprod]; exact hM'
  rw [Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (hne i hi)), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ∈ S := by simpa using hi
  have h0 := hne i hi
  have hD : (D : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hx : x i ≠ 0 := right_ne_zero_of_mul h0
  refine max_le ?_ ?_
  · have := Real.log_nonpos (norm_nonneg _) (b_ultra_int (hint i hi'))
    linarith
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hx)]
    have := Real.log_nonpos (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one Ω D)
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bcoef
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_egf :
    ∀ (N a : ℕ), 0 < N → (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) * (PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ) - 1) = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) := by
  intro N a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := congrArg (PowerSeries.rescale (N : ℚ)) (Polynomial.bernoulli_generating_function ((a : ℚ) / N))
  rw [map_mul, map_mul, map_sub, map_one, PowerSeries.rescale_mk, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale] at h
  have hc : ((a : ℚ) / N) * N = a := by field_simp
  rw [hc] at h
  beta_reduce at h
  have hmk : (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) =
      PowerSeries.C (1 / (N : ℚ)) * PowerSeries.mk (fun n => (N : ℚ) ^ n *
        (Polynomial.aeval ((a : ℚ) / N)) ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [bcoef, map_smul, Polynomial.coe_aeval_eq_eval, smul_eq_mul]
    rw [zpow_sub_one₀ hN', zpow_natCast]
    have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
  rw [hmk, mul_assoc, h, ← mul_assoc, ← mul_assoc, ← map_mul, one_div_mul_cancel hN', map_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BernoulliPolyReflection
section
open Finset UpperTheory.V.Bern

private theorem bernoulli_poly_reflection (k : ℕ) (x : ℚ) :
    (Polynomial.bernoulli k).eval (1 - x) = (-1) ^ k * (Polynomial.bernoulli k).eval x := by
  exact Polynomial.bernoulli_eval_one_sub k x

theorem UpperTheory.V.Bern.b_shift :
    ∀ (N k a : ℕ), 0 < N → bcoef N k (a + N) = bcoef N k a + (k : ℚ) * (a : ℚ) ^ (k - 1) ∧ (∀ m : ℕ, 0 < m → bcoef (m * N) k (m * a) = (m : ℚ) ^ ((k : ℤ) - 1) * bcoef N k a) ∧ (a ≤ N → bcoef N k (N - a) = (-1) ^ k * bcoef N k a) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold bcoef
    have e : ((a + N : ℕ) : ℚ) / N = 1 + (a : ℚ) / N := by
      push_cast; field_simp; ring
    rw [e, Polynomial.bernoulli_eval_one_add, mul_add]
    congr 1
    rcases k with _ | k
    · simp
    · have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this, zpow_natCast, Nat.add_sub_cancel, div_pow]
      field_simp
  · intro m hm
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold bcoef
    have e : ((m * a : ℕ) : ℚ) / ((m * N : ℕ) : ℚ) = (a : ℚ) / N := by
      push_cast; field_simp
    rw [e, Nat.cast_mul, mul_zpow, mul_assoc]
  · intro h
    unfold bcoef
    have e : ((N - a : ℕ) : ℚ) / N = 1 - (a : ℚ) / N := by
      rw [Nat.cast_sub h]; field_simp
    rw [e, bernoulli_poly_reflection]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Charbij
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_charbij :
    ∀ {N : ℕ} [NeZero N] {K Ω : Type} [Field K] [Field Ω] [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)] (f : K →+* Ω) (P : Set (Subgroup (ZMod N)ˣ)), Set.BijOn (fun χ : DirichletCharacter K N => (χ.ringHomComp f : DirichletCharacter Ω N)) (charSet K P) (charSet Ω P) := by
  intro N _ K Ω _ _ _ f P
  have hf : Function.Injective f := f.injective
  have hker : ∀ χ : DirichletCharacter K N, (MulChar.toUnitHom (χ.ringHomComp f)).ker = (MulChar.toUnitHom χ).ker := by
    intro χ
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simp only [charSet, Set.mem_setOf_eq] at hχ ⊢
    rw [hker]
    exact hχ
  · intro χ₁ _ χ₂ _ h
    ext u
    have h' := congrArg (fun ψ : DirichletCharacter Ω N => ψ u) h
    simp only [MulChar.ringHomComp_apply] at h'
    exact hf h'
  · intro χ' hχ'
    have he : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent (ZMod N)ˣ)
    have hne : (primitiveRoots (Monoid.exponent (ZMod N)ˣ) K).Nonempty :=
      ⟨ζ, (mem_primitiveRoots (NeZero.pos _)).mpr hζ⟩
    have hmem : ∀ u, MulChar.toUnitHom χ' u ∈ rootsOfUnity (Monoid.exponent (ZMod N)ˣ) Ω := by
      intro u
      rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    let ψ : (ZMod N)ˣ →* Kˣ := (rootsOfUnity (Monoid.exponent (ZMod N)ˣ) K).subtype.comp
      ((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm.toMonoidHom.comp
        ((MulChar.toUnitHom χ').codRestrict _ hmem))
    have hcomp : (MulChar.ofUnitHom ψ).ringHomComp f = χ' := by
      ext u
      rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe]
      show f (((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm ⟨MulChar.toUnitHom χ' u, hmem u⟩ : Kˣ) : K) = χ' u
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp [MulChar.coe_toUnitHom]
    refine ⟨MulChar.ofUnitHom ψ, ?_, hcomp⟩
    simp only [charSet, Set.mem_setOf_eq] at hχ' ⊢
    rw [← hker, hcomp]
    exact hχ'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap
section
open Finset UpperTheory.V.Bern

private theorem change_level_value_eq {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S)
    {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N) (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f) (a : ℕ) :
    ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst hde
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f = DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ : ψ = φ.ringHomComp f := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  subst hψ
  simp [MulChar.ringHomComp_apply]

theorem UpperTheory.V.Bern.b_condmap :
    ∀ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ χ : DirichletCharacter R N, DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor ∧ (∀ a : ℕ, primVal (χ.ringHomComp f) a = f (primVal χ a)) ∧ (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  intro R S _ _ N _ f hf χ
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [← hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
  have hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
    unfold DirichletCharacter.conductor
    rw [hset]
  refine ⟨hcond, ?_, hker⟩
  intro a
  unfold primVal
  exact change_level_value_eq f hcond χ.conductor_dvd_level (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f))
    χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f))
    (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_primitiveCharacter]) a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_expand :
    ∀ (N k a : ℕ), 0 < N → bcoef N k a = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * bernoulli j * (N : ℚ) ^ ((j : ℤ) - 1) * (a : ℚ) ^ (k - j) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [bcoef]
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Polynomial.eval_monomial, div_pow]
  have hsplit : (N : ℚ) ^ ((k : ℤ) - 1) = (N : ℚ) ^ ((j : ℤ) - 1) * (N : ℚ) ^ ((k - j : ℕ) : ℤ) := by
    rw [← zpow_add₀ hN']
    congr 1
    push_cast [hjk]
    ring
  rw [hsplit, zpow_natCast]
  have hp : (N : ℚ) ^ (k - j) ≠ 0 := pow_ne_zero _ hN'
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.GaussMulGaussInv
section
open Finset UpperTheory.V.Bern

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hF : ZMod.dft (⇑χ) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ ZMod.stdAddChar :=
    funext fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h1 := congr_fun (ZMod.dft_dft (⇑χ)) 1
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at h1
  simp only at h1
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, neg_neg, AddChar.mulShift_one,
    smul_eq_mul] at h1
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [mul_comm (gaussSum χ _), h1, mul_assoc, hsq, mul_one]

private theorem conj_gauss {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) := by
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (-1)
  rw [inv_inv, Units.val_neg, Units.val_one] at h
  rw [starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift, h, mul_comm]

theorem UpperTheory.V.Bern.b_gauss :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N ∧ ‖χ.rootNumber‖ = 1 := by
  intro N _ χ hχ
  have hns : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = N := by
    rw [← Complex.mul_conj, conj_gauss, ← mul_assoc, gauss_mul_gauss_inv χ hχ]
  have hns' : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by exact_mod_cast hns
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by
    rw [Complex.norm_def, hns']
  refine ⟨hg, ?_⟩
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one,
    hg, Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  rw [show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_ne_zero'.mpr hpos)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_parity :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter Ω N), (χ.toUnitHom.ker ∈ parKer N k ↔ χ (-1) = (-1) ^ k) ∧ (χ.primitiveCharacter (-1) = χ (-1)) := by
  intro Ω _ _ N _ k χ
  have hne : (-1 : Ω) ≠ 1 := by norm_num
  refine ⟨?_, ?_⟩
  · have hval : χ.toUnitHom (-1) = 1 ↔ χ (-1) = 1 := by
      rw [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_one]
    show ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker ↔ Even k) ↔ _
    rw [MonoidHom.mem_ker, hval]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]
      simp [hk]
    · rw [hk.neg_one_pow]
      have hk' : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      rcases χ.even_or_odd with h | h
      · have h1 : χ (-1) = 1 := h
        simp [hk', h1, hne.symm]
      · have h1 : χ (-1) = -1 := h
        simp [hk', h1, hne]
  · have hd := DirichletCharacter.conductor_dvd_level χ
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hd (-1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, Units.val_neg, Units.val_one,
      ZMod.cast_neg hd, ZMod.cast_one hd] at h
    exact h.symm
end

