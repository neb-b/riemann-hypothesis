module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfForallNhds
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.Twist.FockLogDeriv

theorem eq_zero_of_forall_nhds {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (y₀ : V) (U : Set V) (hU : U ∈ 𝓝 y₀) (b : V) (hb : ∀ y ∈ U, T y b = 0) : b = 0 := by
  apply hT
  intro z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have h0 : T y₀ b = 0 := hb y₀ (hball (Metric.mem_ball_self hε))
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  set t : ℝ := ε / (2 * (‖z‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have htz : t * (‖z‖ + 1) = ε / 2 := by
    rw [ht]; field_simp
  have hmem : y₀ + t • z ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    nlinarith [norm_nonneg z]
  have h1 := hb _ hmem
  rw [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, h0, zero_add, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left htpos.ne'

theorem main {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (Jm : V × V →ₗ[ℝ] V × V) (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (hE : ∀ (p : V × V) (y : V), fderiv ℝ f₀ y (Jm p).1
        + (-(2 * Real.pi * Complex.I)) * ((T y (Jm p).2 : ℝ) : ℂ) * f₀ y
      = Complex.I * (fderiv ℝ f₀ y p.1
        + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y)) :
    ∃ m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ, ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y := by
  let Φ : V × V →ₗ[ℝ] (V → ℂ) :=
    { toFun := fun p y => fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y
      map_add' := by
        intro p q
        funext y
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Complex.ofReal_add, Pi.add_apply]
        ring
      map_smul' := by
        intro s p
        funext y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Pi.smul_apply, Complex.real_smul]
        ring }
  have hΦ : ∀ p y, Φ p y = fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y :=
    fun p y => rfl
  have hEΦ : ∀ p y, Φ (Jm p) y = Complex.I * Φ p y := fun p y => by rw [hΦ, hΦ]; exact hE p y
  have hΦ0 : ∀ w y, Φ (0, w) y = (-(2 * Real.pi * Complex.I)) * ((T y w : ℝ) : ℂ) * f₀ y := by
    intro w y
    rw [hΦ]
    simp only [map_zero, zero_add]
  let Q : V × V →ₗ[ℝ] V × V :=
    (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.fst ℝ V V) + Jm ∘ₗ (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.snd ℝ V V)
  let Θ : V × V →ₗ[ℝ] (V → ℂ) := Φ ∘ₗ Q
  have hΘ : ∀ w₁ w₂ y, Θ (w₁, w₂) y = (-(2 * Real.pi * Complex.I)) * ((T y w₁ : ℝ) : ℂ) * f₀ y +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y w₂ : ℝ) : ℂ) * f₀ y) := by
    intro w₁ w₂ y
    have e : Θ (w₁, w₂) = Φ (0, w₁) + Φ (Jm (0, w₂)) := map_add Φ _ _
    rw [e, Pi.add_apply, hEΦ, hΦ0, hΦ0]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, f₀ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (SchwartzMap.ext fun y => by simp [h y])
  have hU : {y | f₀ y ≠ 0} ∈ 𝓝 y₀ := (isOpen_compl_singleton.preimage f₀.continuous).mem_nhds hy₀
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w₁, w₂⟩ h
    have hsplit : ∀ y ∈ {y | f₀ y ≠ 0}, T y w₁ = 0 ∧ T y w₂ = 0 := by
      intro y hy
      have h0 : Θ (w₁, w₂) y = 0 := by rw [h]; rfl
      rw [hΘ] at h0
      have h3 : ((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ) = 0 := by
        have h4 : (-(2 * Real.pi * Complex.I)) * f₀ y *
            (((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ)) = 0 := by
          rw [← h0]; ring
        rcases mul_eq_zero.mp h4 with h5 | h5
        · rcases mul_eq_zero.mp h5 with h6 | h6
          · exact absurd h6 hc
          · exact absurd h6 hy
        · exact h5
      have hre := congrArg Complex.re h3
      have him := congrArg Complex.im h3
      simp at hre him
      exact ⟨hre, him⟩
    have e1 := eq_zero_of_forall_nhds T hT y₀ _ hU w₁ fun y hy => (hsplit y hy).1
    have e2 := eq_zero_of_forall_nhds T hT y₀ _ hU w₂ fun y hy => (hsplit y hy).2
    rw [e1, e2]; rfl
  have hle : LinearMap.range Θ ≤ LinearMap.range Φ := LinearMap.range_comp_le_range Q Φ
  have hrange : LinearMap.range Θ = LinearMap.range Φ := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [LinearMap.finrank_range_of_inj hinj]
    exact LinearMap.finrank_range_le Φ
  have hmem : ∀ a, (Φ ∘ₗ LinearMap.inl ℝ V V) a ∈ LinearMap.range Θ := fun a => by
    rw [hrange]; exact LinearMap.mem_range_self Φ _
  let e := LinearEquiv.ofInjective Θ hinj
  let W : V →ₗ[ℝ] V × V :=
    e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range Θ) (Φ ∘ₗ LinearMap.inl ℝ V V) hmem
  have hW : ∀ a, Θ (W a) = Φ (a, 0) := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨Φ (a, 0), hmem a⟩)
    exact h
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun a y => (-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ)))
    (by intro a₁ a₂ y; simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
    (by intro a y₁ y₂; simp only [map_add (f := _), LinearMap.add_apply, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
  refine ⟨m, fun a y => ?_⟩
  have h1 : Φ (a, 0) y = fderiv ℝ f₀ y a := by
    rw [hΦ]; simp only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  have h2 := hΘ (W a).1 (W a).2 y
  rw [Prod.mk.eta, hW, h1] at h2
  rw [h2]
  show _ = ((-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ))) * f₀ y
  ring

end GlobalTheory.CompanionTheory.Twist.FockLogDeriv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SchwartzLogDerivLinearGaussian
section
namespace GlobalTheory.CompanionTheory.Twist

theorem schwartz_logDeriv_linear_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : SchwartzMap V ℂ) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) (y : V) :
    f₀ y = f₀ 0 * Complex.exp (m y y / 2) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y)) ((t : ℂ) * m y y * f₀ (t • y)) t := by
    intro t
    have h1 : HasFDerivAt f₀ (fderiv ℝ f₀ (t • y)) (t • y) := f₀.differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h3 : HasDerivAt (fun s : ℝ => f₀ (s • y)) (fderiv ℝ f₀ (t • y) y) t :=
      h1.comp_hasDerivAt t h2
    rw [hm, map_smul, Complex.real_smul] at h3
    exact h3
  have hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 * m y y / 2)))
      (Complex.exp (-((t : ℂ) ^ 2 * m y y / 2)) * (-((t : ℂ) * m y y))) t := by
    intro t
    have h5 : HasDerivAt (fun z : ℂ => -(z ^ 2 * m y y / 2)) (-((t : ℂ) * m y y)) (t : ℂ) := by
      have h6 := (((hasDerivAt_pow 2 (t : ℂ)).mul_const (m y y)).div_const 2).neg
      refine h6.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact h5.cexp.comp_ofReal
  have hH : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => f₀ (s • y) * Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) 0 t := by
    intro t
    refine ((hg t).mul (hE t)).congr_deriv ?_
    ring
  have h10 := is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) 1 0
  simp only [one_smul, zero_smul, Complex.ofReal_one, Complex.ofReal_zero, one_pow, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero,
    Complex.exp_zero, mul_one] at h10
  calc f₀ y = f₀ y * Complex.exp (-(m y y / 2)) * Complex.exp (m y y / 2) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = f₀ 0 * Complex.exp (m y y / 2) := by rw [h10]

theorem schwartz_logDeriv_linear_gaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) :
    ∃ (c₀ : ℂ) (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), c₀ ≠ 0 ∧ (∀ x, x ≠ 0 → 0 < Q x x) ∧
      ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by
  have hform := fun y => schwartz_logDeriv_linear_formula f₀ m hm y
  have hc0 : f₀ 0 ≠ 0 := by
    intro h0
    apply hf
    ext x
    simp [hform x, h0]
  refine ⟨f₀ 0, (-(1 / 2 : ℝ)) • m.compr₂ Complex.reLm, (-(1 / 2 : ℝ)) • m.compr₂ Complex.imLm,
    hc0, ?_, ?_⟩
  · intro x hx
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, smul_eq_mul]
    by_contra hle
    push Not at hle
    have hre : 0 ≤ (m x x).re := by linarith
    obtain ⟨C, hCpos, hC⟩ := f₀.decay 1 0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcpos : 0 < ‖f₀ 0‖ := norm_pos_iff.mpr hc0
    set t : ℝ := C / (‖f₀ 0‖ * ‖x‖) + 1 with ht
    have htpos : 0 < t := by positivity
    have hlow : ‖f₀ 0‖ ≤ ‖f₀ (t • x)‖ := by
      rw [hform (t • x), norm_mul, Complex.norm_exp]
      apply le_mul_of_one_le_right (norm_nonneg _)
      apply Real.one_le_exp
      simp only [map_smul, LinearMap.smul_apply, smul_smul, Complex.div_ofNat_re, Complex.smul_re,
        smul_eq_mul]
      have h6 := mul_nonneg (mul_self_nonneg t) hre
      linarith
    have hdec := hC (t • x)
    rw [pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hdec
    have hbig : C < t * ‖x‖ * ‖f₀ 0‖ := by
      have hne : ‖f₀ 0‖ * ‖x‖ ≠ 0 := by positivity
      have heq : t * ‖x‖ * ‖f₀ 0‖ = C + ‖x‖ * ‖f₀ 0‖ := by
        rw [ht]
        field_simp
      rw [heq]
      linarith [mul_pos hxpos hcpos]
    have h7 : t * ‖x‖ * ‖f₀ 0‖ ≤ t * ‖x‖ * ‖f₀ (t • x)‖ :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    linarith
  · intro x
    rw [hform x]
    congr 1
    congr 1
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, Complex.imLm_coe,
      smul_eq_mul]
    apply Complex.ext <;> simp <;> ring

end GlobalTheory.CompanionTheory.Twist
end

