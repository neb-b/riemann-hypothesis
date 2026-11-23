module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisFormSumOfGain
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenGainPolynomial

theorem re_inner_self {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) w
  simpa using this

theorem phi_lb (s : ℕ) (c ν x : ℝ) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - c * y ^ 4 ≤ ((1 + y) ^ s)⁻¹) :
    ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * c / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))
      ≤ ((1 + x) ^ s)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have hy1 : -1 < (x - ν) / (1 + ν) := by
    rw [lt_div_iff₀ h1]; linarith
  have hA' := hA _ hy1
  have hx1 : 1 + x = (1 + ν) * (1 + (x - ν) / (1 + ν)) := by field_simp; ring
  have ha : 0 ≤ ((1 + ν) ^ s)⁻¹ := by positivity
  calc _ = ((1 + ν) ^ s)⁻¹ * (1 - s * ((x - ν) / (1 + ν)) + (s : ℝ) ^ 2 / 4 * ((x - ν) / (1 + ν)) ^ 2
          - c * ((x - ν) / (1 + ν)) ^ 4) := by
          field_simp; ring
    _ ≤ ((1 + ν) ^ s)⁻¹ * ((1 + (x - ν) / (1 + ν)) ^ s)⁻¹ := mul_le_mul_of_nonneg_left hA' ha
    _ = ((1 + x) ^ s)⁻¹ := by rw [hx1, mul_pow, mul_inv]

theorem fc_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (ν k0 k1 k2 k4 : ℝ) (w : V) :
    (inner ℂ w (fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) w)).re =
      k0 * ‖w‖ ^ 2 + k1 * (inner ℂ w (fc b μ (fun x => x - ν) w)).re
        + k2 * ‖fc b μ (fun x => x - ν) w‖ ^ 2
        + k4 * ‖fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) w)‖ ^ 2 := by
  have e1 : ∀ (k : ℝ) (f : ℝ → ℝ), fc b μ (fun x => k * f x) = (k : ℂ) • fc b μ f := by
    intro k f
    calc fc b μ (fun x => k * f x) = fc b μ (fun _ => k) * fc b μ f := hmul (fun _ => k) f
      _ = (k : ℂ) • fc b μ f := by rw [hconst, smul_mul_assoc, one_mul]
  have hT2 : fc b μ (fun x => (x - ν) * (x - ν)) = fc b μ (fun x => x - ν) * fc b μ (fun x => x - ν) :=
    hmul (fun x => x - ν) (fun x => x - ν)
  have hT4 : fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) =
      fc b μ (fun x => (x - ν) * (x - ν)) * fc b μ (fun x => (x - ν) * (x - ν)) :=
    hmul (fun x => (x - ν) * (x - ν)) (fun x => (x - ν) * (x - ν))
  have hF : fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) =
      (k0 : ℂ) • 1 + (k1 : ℂ) • fc b μ (fun x => x - ν) + (k2 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν))
        + (k4 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) := by
    rw [hadd (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν)))
        (fun x => k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))),
      hadd (fun x => k0 + k1 * (x - ν)) (fun x => k2 * ((x - ν) * (x - ν))),
      hadd (fun _ => k0) (fun x => k1 * (x - ν)), hconst,
      e1 k1 (fun x => x - ν), e1 k2 (fun x => (x - ν) * (x - ν)),
      e1 k4 (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν)))]
  rw [hF, hT4, hT2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have r2 : ∀ u : V, inner ℂ u (fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) u)) =
      inner ℂ (fc b μ (fun x => x - ν) u) (fc b μ (fun x => x - ν) u) := fun u => (hsym _ _ _).symm
  have r4 := (hsym (fun x => x - ν) w _).symm.trans (r2 (fc b μ (fun x => x - ν) w))
  rw [r4, r2]
  simp only [re_inner_self]

theorem main {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (hid : fc b μ (fun x => x) = casimirK ε E)
    (κ c : ℝ) (s : ℕ) (c0 C cs ν : ℝ) (hc0 : 0 < c0) (hC : 0 ≤ C) (hcs0 : 0 ≤ cs)
    (hsC : c + 1 ≤ (s : ℝ) ^ 2 * c0 / 4 - s * C)
    (hν0 : 0 ≤ ν) (hνc : cs * C ≤ ν) (v : V) (hv : Eig ε E ν v)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - cs * y ^ 4 ≤ ((1 + y) ^ s)⁻¹)
    (hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2)
    (h8 : c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2)
    (h9a : ‖∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)‖ ≤ C * (1 + ν) * ‖v‖ ^ 2)
    (h9b : ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ C * (1 + ν) ^ 3 * ‖v‖ ^ 2) :
    ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have ha : 0 < ((1 + ν) ^ s)⁻¹ := by positivity
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hT : ∀ u, fc b μ (fun x => x - ν) u = casimirK ε E u - (ν : ℂ) • u := by
    intro u
    have hf : (fun x : ℝ => x - ν) = fun x => x + -ν := by funext x; ring
    rw [hf, hadd (fun x => x) (fun _ => -ν), hid, hconst]
    simp [sub_eq_add_neg]
  have hTE : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (E p.1 p.2 v) = Z ε E p.1 p.2 v := by
    intro p
    rw [hT, Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hTZ : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (Z ε E p.1 p.2 v) =
      (casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v := by
    intro p
    rw [hT, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hp : ∀ p ∈ nc ε,
      ((1 + ν) ^ s)⁻¹ * ‖E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)).re
        + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ‖Z ε E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4))
          * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ (inner ℂ (E p.1 p.2 v) (fc b μ (fun x => ((1 + x) ^ s)⁻¹) (E p.1 p.2 v))).re := by
    intro p _
    have := hmono (fun x => ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν))))
      (fun x => ((1 + x) ^ s)⁻¹) (fun x hx => phi_lb s cs ν x hν0 hx hA) (E p.1 p.2 v)
    rw [fc_poly hsym hadd hmul hconst, hTE, hTZ] at this
    exact this
  unfold beta
  rw [Complex.re_sum]
  refine le_trans ?_ (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum, hE]
  have hN : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hR := le_trans (Complex.re_le_norm _) h9a
  have hk1 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * s / (1 + ν) := by positivity
    linarith
  have hk2 : 0 ≤ ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) := by positivity
  have hk4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4 := by positivity
    linarith
  have i2 := mul_le_mul_of_nonpos_left hR hk1
  have i3 := mul_le_mul_of_nonneg_left h8 hk2
  have i4 := mul_le_mul_of_nonpos_left h9b hk4
  have e2 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) * (C * (1 + ν) * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (s * C) * ‖v‖ ^ 2) := by
    field_simp
  have e3 : ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) * (c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2)
      = ((1 + ν) ^ s)⁻¹ * ((s : ℝ) ^ 2 * c0 / 4) * ‖v‖ ^ 2 := by
    field_simp
  have e4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) * (C * (1 + ν) ^ 3 * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (cs * C / (1 + ν)) * ‖v‖ ^ 2) := by
    field_simp
  rw [e2] at i2
  rw [e3] at i3
  rw [e4] at i4
  have b4 : cs * C / (1 + ν) ≤ 1 := (div_le_one h1).2 (by linarith)
  have hb4 := mul_le_mul_of_nonneg_left b4 (mul_nonneg ha.le hN)
  have hs := mul_le_mul_of_nonneg_left hsC (mul_nonneg ha.le hN)
  nlinarith

end EigenGainPolynomial

theorem eigen_gain_of_moments : A0 → A8 → A9 → A10 → FunctionalCalculusLaws → A12 := by
  intro h0 h8 h9 h10 h11 n ε V _ _ E hM ι b μ hB κ hκ c hc
  obtain ⟨-, -, -, hnorm⟩ := h0 n ε V E hM
  obtain ⟨c0, x1, hc0, h8'⟩ := h8 n ε V E hM
  obtain ⟨C, hC, h9'⟩ := h9 n ε V E hM
  obtain ⟨-, hsym, hmono, hadd, hmul, hconst, hid⟩ := h11 n ε V E hM ι b μ hB
  obtain ⟨cs, hcs, h10'⟩ := h10 (⌈4 * (C + c + 1) / c0⌉₊ + 1) (by omega)
  refine ⟨⌈4 * (C + c + 1) / c0⌉₊ + 1, max 0 (max x1 (cs * C)), by omega, le_max_left _ _, ?_⟩
  intro ν v hν hv
  have hν0 : 0 ≤ ν := le_trans (le_max_left _ _) hν
  have hνx : x1 ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hν
  have hνc : cs * C ≤ ν := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hν
  have hsC : c + 1 ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) ^ 2 * c0 / 4
      - ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * C := by
    have hce := Nat.le_ceil (4 * (C + c + 1) / c0)
    have hsc : 4 * (C + c + 1) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * c0 := by
      have := (div_le_iff₀ hc0).1 hce
      push_cast
      nlinarith
    have hs1 : (1 : ℝ) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * (C + c + 1) / c0⌉₊]
    nlinarith
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2 := by
    rw [(hnorm κ hκ v).2.1, hv', inner_smul_right, Complex.re_ofReal_mul, EigenGainPolynomial.re_inner_self]
    ring
  obtain ⟨h9a, h9b⟩ := h9' ν v hν0 hv
  exact EigenGainPolynomial.main hsym hmono hadd hmul hconst hid κ c _ c0 C cs ν hc0 hC hcs hsC hν0 hνc v hv h10'
    hE (h8' ν v hνx hv) h9a h9b

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisSumOfOrthogonality
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace FormEigenMonotone

lemma phi_nonneg (s : ℕ) (R x : ℝ) : 0 ≤ phiR s R x := le_max_right _ _

lemma phi_zero {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : R ≤ x) : phiR s R x = 0 := by
  unfold phiR
  apply max_eq_right
  have h1 : (0:ℝ) < (1+R)^s := by positivity
  have h2 : (1+R)^s ≤ (1+x)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith

lemma phi_le_one {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) : phiR s R x ≤ 1 := by
  unfold phiR
  apply max_le _ zero_le_one
  have h1 : (1:ℝ) ≤ (1+x)^s := one_le_pow₀ (by linarith)
  have h2 : ((1+x)^s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have h3 : 0 ≤ ((1+R)^s)⁻¹ := by positivity
  linarith

lemma phi_eq {s : ℕ} {R x : ℝ} (hx : 0 ≤ x) (hxR : x < R) :
    phiR s R x = ((1+x)^s)⁻¹ - ((1+R)^s)⁻¹ := by
  unfold phiR
  apply max_eq_left
  have h1 : (0:ℝ) < (1+x)^s := by positivity
  have h2 : (1+x)^s ≤ (1+R)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}

lemma beta_add (A B : Module.End ℂ V) (v w : V) :
    beta ε E (A + B) v w = beta ε E A v w + beta ε E B v w := by
  simp only [beta, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]

lemma re_inner_smul_self (r : ℝ) (v : V) : (inner ℂ v ((r : ℂ) • v)).re = r * ‖v‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

lemma beta_const_re (r : ℝ) (v : V) :
    (beta ε E ((r : ℂ) • 1) v v).re = r * ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 := by
  simp only [beta, LinearMap.smul_apply, Module.End.one_apply, Complex.re_sum, re_inner_smul_self,
    Finset.mul_sum]

lemma beta_mono
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (φ ψ : ℝ → ℝ) (h : ∀ x, 0 ≤ x → φ x ≤ ψ x) (v : V) :
    (beta ε E (fc b μ φ) v v).re ≤ (beta ε E (fc b μ ψ) v v).re := by
  simp only [beta, Complex.re_sum]
  exact Finset.sum_le_sum fun p _ => hmono φ ψ h _

lemma norm_fib (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (F : Finset ι) :
    ‖∑ j ∈ F, starRingEnd ℂ (f (b j)) • b j‖ ^ 2 = ∑ j ∈ F, ‖f (b j)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, hb.inner_sum, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_conj, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma eig_fib (hb : ∀ i, Eig ε E (μ i) (b i)) (ν : ℝ) (F : Finset ι) (hF : ∀ j ∈ F, μ j = ν)
    (a : ι → ℂ) : Eig ε E ν (∑ j ∈ F, a j • b j) := by
  unfold Eig
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_smul, hb j, hF j hj, smul_comm]

lemma key {κ c x₀ R : ℝ} {s : ℕ}
    (hA0 : ∀ w, ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1)
    (hA12 : ∀ ν v, x₀ ≤ ν → Eig ε E ν v →
      ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re)
    (hc : 0 ≤ c) (hR : 0 < R) (ν : ℝ) (hν : 0 ≤ ν) (h : V) (hh : Eig ε E ν h) :
    phiR s R ν * (ν - κ + c) * ‖h‖ ^ 2 - (if ν < x₀ then x₀ + |κ| + c else 0) * ‖h‖ ^ 2 ≤
      (beta ε E (fc b μ (phiR s R)) h h).re := by
  have hN : ∀ w, 0 ≤ (beta ε E (fc b μ (phiR s R)) w w).re := by
    intro w
    have h0 := beta_mono (ε := ε) (E := E) hmono (fun _ => (0:ℝ)) (phiR s R)
      (fun x _ => phi_nonneg s R x) w
    rw [hconst 0, beta_const_re] at h0
    simpa using h0
  have hd0 : (0:ℝ) ≤ ((1 + R) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) _)
  have hS : ∑ p ∈ nc ε, ‖E p.1 p.2 h‖ ^ 2 = (ν - κ) * ‖h‖ ^ 2 := by
    rw [hA0 h, show casimirK ε E h = (ν : ℂ) • h from hh, re_inner_smul_self]
    ring
  have hlow : (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) h h).re - ((1 + R) ^ s)⁻¹ * ((ν - κ) * ‖h‖ ^ 2)
      ≤ (beta ε E (fc b μ (phiR s R)) h h).re := by
    have e : fc b μ (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
        = fc b μ (fun x => ((1 + x) ^ s)⁻¹) + fc b μ (fun _ => -((1 + R) ^ s)⁻¹) := hadd _ _
    have h1 := beta_mono (ε := ε) (E := E) hmono (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
      (phiR s R) (fun x _ => by
        simp only [phiR]
        linarith [le_max_left (((1 + x) ^ s)⁻¹ - ((1 + R) ^ s)⁻¹) 0]) h
    rw [e, beta_add, hconst (-((1 + R) ^ s)⁻¹), Complex.add_re, beta_const_re, hS] at h1
    linarith
  have hn : 0 ≤ ‖h‖ ^ 2 := by positivity
  by_cases hx : ν < x₀
  · rw [if_pos hx]
    have hp0 := phi_nonneg s R ν
    have hp1 := phi_le_one (s := s) hR hν
    have hbd : phiR s R ν * (ν - κ + c) ≤ x₀ + |κ| + c := by
      rcases le_total 0 (ν - κ + c) with h0 | h0
      · nlinarith [neg_le_abs κ, mul_le_mul_of_nonneg_right hp1 h0]
      · nlinarith [abs_nonneg κ, mul_nonpos_of_nonneg_of_nonpos hp0 h0]
    have := mul_le_mul_of_nonneg_right hbd hn
    linarith [hN h]
  · rw [if_neg hx]
    have hA := hA12 ν h (not_lt.mp hx) hh
    by_cases hνR : ν < R
    · rw [phi_eq hν hνR]
      nlinarith [hlow, mul_nonneg (mul_nonneg hd0 hc) hn]
    · rw [phi_zero hR (not_lt.mp hνR)]
      simpa using hN h

end FormEigenMonotone

theorem basis_form_sum_of_gain : A0 → FunctionalCalculusLaws → A12 → BasisSumAsFormValues → A13 := by
  intro hA0 hA11 hA12 hA13a
  unfold A0 FunctionalCalculusLaws A12 BasisSumAsFormValues A13 ForBas ForMod at *
  intro n ε V i1 i2 E hM ι b μ hEB κ hκ c hc
  obtain ⟨-, -, hmono, hadd, -, hconst, -⟩ := hA11 n ε V E hM ι b μ hEB
  obtain ⟨s, x₀, hs, hx₀, hb12⟩ := hA12 n ε V E hM ι b μ hEB κ hκ c hc
  have hA0' := fun w => ((hA0 n ε V E hM).2.2.2 κ hκ w).2.1
  have hK : 0 ≤ x₀ + |κ| + c := by linarith [abs_nonneg κ]
  refine ⟨s, x₀, x₀ + |κ| + c, hs, hK, ?_⟩
  intro R f S T hS hT
  have hTb : 0 ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 :=
    mul_nonneg hK (Finset.sum_nonneg fun i _ => by positivity)
  rcases le_or_gt R 0 with hR | hR
  · have hSe : ∀ i ∈ S, False := fun i hi => by
      have := (hS i).1 hi
      linarith [hEB.nonneg i]
    rw [Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) * ‖f (b i)‖ ^ 2)
        (fun i hi => (hSe i hi).elim),
      Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) *
        (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2))
        (fun i hi => (hSe i hi).elim)]
    linarith
  · have hφS : ∀ i ∉ S, phiR s R (μ i) = 0 := fun i hi =>
      FormEigenMonotone.phi_zero hR (not_lt.mp fun h => hi ((hS i).2 h))
    obtain ⟨T', hST', hT'⟩ := hA13a n ε V E hM ι b μ hEB (phiR s R) S hφS
    have key1 := hT' f
    have hstep : ∀ ν ∈ Finset.image μ T',
        (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2 ≤
        (beta ε E (fc b μ (phiR s R)) (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)
            (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)).re := by
      intro ν hν
      obtain ⟨j0, -, rfl⟩ := Finset.mem_image.1 hν
      have hEig := FormEigenMonotone.eig_fib hEB.eig (μ j0) (T'.filter fun j => μ j = μ j0)
        (fun j hj => (Finset.mem_filter.1 hj).2) (fun j => (starRingEnd ℂ) (f (b j)))
      beta_reduce at hEig
      have hk := FormEigenMonotone.key (b := b) (μ := μ) hA0' hmono hadd hconst hb12 hc hR (μ j0)
        (hEB.nonneg j0) _ hEig
      rw [FormEigenMonotone.norm_fib hEB.on f] at hk
      linarith
    have hsum1 : ∑ ν ∈ Finset.image μ T', (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2
        = ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2 := by
      apply Finset.sum_image'
      intro i _
      beta_reduce
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.1 hj).2]
    have e := Finset.sum_subset hST' (f := fun j => phiR s R (μ j) * (μ j - κ + c) * ‖f (b j)‖ ^ 2)
      (fun j _ hj => by simp only [hφS j hj, zero_mul])
    have hsplit : ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2
        = ∑ j ∈ S, phiR s R (μ j) * (μ j - κ) * ‖f (b j)‖ ^ 2 +
            c * ∑ j ∈ S, phiR s R (μ j) * ‖f (b j)‖ ^ 2
          - ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      congr 1
      rw [← e, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hTb2 : ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
        ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
          = ∑ j ∈ T' with μ j < x₀, (x₀ + |κ| + c) * ‖f (b j)‖ ^ 2 := by
            rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        _ ≤ ∑ i ∈ T, (x₀ + |κ| + c) * ‖f (b i)‖ ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact (hT j).2 (Finset.mem_filter.1 hj).2
            · intro j _ _
              exact mul_nonneg hK (by positivity)
    have hle := Finset.sum_le_sum hstep
    rw [hsum1, hsplit, ← key1] at hle
    have hR2 : ∑ i ∈ S, phiR s R (μ i) *
          (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2)
        = ∑ i ∈ S, phiR s R (μ i) * ∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2
          - ∑ i ∈ S, phiR s R (μ i) * (μ i - κ) * ‖f (b i)‖ ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR2]
    linarith

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirPowerCommute
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace AdjointWordFiltration

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem U_mono (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  unfold U
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

theorem word_mem (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) :
    (l.map fun p => E p.1 p.2).prod ∈ U E l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩

theorem mul_E_mem (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) {j : ℕ} {w : Module.End ℂ V}
    (hw : w ∈ U E j) : w * E a b ∈ U E (j + 1) := by
  unfold U at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l ++ [(a, b)], by simp; omega, ?_⟩
    simp [List.prod_append]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem adjSign_mul_self (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign; split_ifs <;> norm_num

theorem word_adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (l : List (Fin n × Fin n)) :
    ∃ u' ∈ U E l.length, ∀ x y, inner ℂ x ((l.map fun p => E p.1 p.2).prod y) = inner ℂ (u' x) y := by
  induction l with
  | nil =>
    refine ⟨1, by simpa using word_mem E [], fun x y => ?_⟩
    simp
  | cons p t ih =>
    obtain ⟨w', hw', hw⟩ := ih
    refine ⟨(starRingEnd ℂ (adjSign ε p.2 p.1)) • (w' * E p.2 p.1), ?_, fun x y => ?_⟩
    · exact Submodule.smul_mem _ _ (by simpa using mul_E_mem E p.2 p.1 hw')
    · have h1 := hu p.2 p.1 x ((t.map fun p => E p.1 p.2).prod y)
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.smul_apply, inner_smul_left,
        Complex.conj_conj, Module.End.mul_apply, ← hw, h1, ← mul_assoc, adjSign_mul_self, one_mul]

end AdjointWordFiltration

theorem adjoint_stable_filtration : FiltrationAdjointStable := by
  intro n ε V _ _ E hM k u hu
  unfold U at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨u', hu', h⟩ := AdjointWordFiltration.word_adj ε E hM.uni l
    exact ⟨u', AdjointWordFiltration.U_mono E hl hu', h⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun x y => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx⟩ := hx
    obtain ⟨y', hy', hy⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', fun a b => by
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hx, hy]⟩
  | smul c x _ hx =>
    obtain ⟨x', hx', hx⟩ := hx
    refine ⟨starRingEnd ℂ c • x', Submodule.smul_mem _ _ hx', fun a b => ?_⟩
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_conj, hx]

end PositivityTheory.CW

end
end

