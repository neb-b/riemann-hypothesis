module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyExact

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.HNsmulNsmul
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

lemma kappa_real : conj (repKappa a b d ha hd lam hlam) = repKappa a b d ha hd lam hlam := by
  unfold repKappa
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_natCast]

lemma not_dvd_mul' {l : ℕ} (hl : l.Prime) {u v : ℤ} (hu : ¬ (l : ℤ) ∣ u) (hv : ¬ (l : ℤ) ∣ v) :
    ¬ (l : ℤ) ∣ u * v := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd h with h1 | h1
  · exact hu h1
  · exact hv h1

lemma H_nsmul_nsmul (L : PeriodPair) (s t : ℕ) (v w : m → ℂ) :
    stdH L m (s • v) (t • w) = (s : ℂ) * t * stdH L m v w := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Pi.mul_apply, Pi.natCast_apply, map_mul, map_natCast]
    ring

lemma H_self_ne (L : PeriodPair) {v : m → ℂ} (hv : v ≠ 0) : stdH L m v v ≠ 0 := by
  rw [stdH_apply]
  have hA : area L ≠ 0 := by rw [area_eq]; exact abs_ne_zero.mpr (detD_ne L)
  refine mul_ne_zero ?_ (inv_ne_zero (by exact_mod_cast hA))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by by_contra h; push_neg at h; exact hv (funext h)
  have hsum : (∑ j, v j * conj (v j)) = ((∑ j, Complex.normSq (v j) : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun j _ => Complex.mul_conj (v j)
  rw [hsum]
  have : 0 < ∑ j, Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  exact_mod_cast this.ne'

variable {a b c d ha hd lam hlam m}

lemma sat_norm (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) :
    ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧ stdH (cmL a b d ha hd lam hlam) m v v = repKappa a b d ha hd lam hlam * p / q := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨n, hn⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  refine ⟨n, (s : ℤ) * s, not_dvd_mul' hl hs' hs', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn

lemma sat_pair (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) :
    ∃ n c₂ s : ℤ, ¬ (l : ℤ) ∣ s ∧ stdH (cmL a b d ha hd lam hlam) m v w =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨t, ht, htw⟩ := hw
  obtain ⟨n, c₂, hn, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv htw
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  have ht' : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => ht (by exact_mod_cast h)
  refine ⟨n, c₂, (s : ℤ) * t, not_dvd_mul' hl hs' ht', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h; apply ht; rw [show t = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn

lemma im_pi_inv (n c₂ : ℤ) :
    ((2 * cmTheta b d - b)⁻¹ * (repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)))).im =
      -((2 * n - c₂ * b : ℤ) : ℝ) / d := by
  rw [rep_kappa_eq]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 hd').ne'
  have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd'.le
  have hpi : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    unfold cmTheta
    ring
  have hconj : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
    unfold cmTheta
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hpi, hconj]
  simp [Complex.mul_im, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq, Complex.div_re,
    Complex.div_im]
  field_simp
  rw [show (Real.sqrt d) ^ 2 = d by rw [sq]; exact hsq] at *
  ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKey
section
namespace PI.UnitaryGroupMassFormula.UnimodLocStd

theorem keyRep_of_start (hS : KeyStart) : KeyRep := keyRep_of hS keyNewton keyExact

end PI.UnitaryGroupMassFormula.UnimodLocStd
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepPrimPair
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_coord (a : ℕ) (ha : 0 < a) (b : ℤ) (d : ℕ) (hd : 0 < d) (p q r s : ℝ)
    (h : (p : ℂ) * a + q * cmTheta b d = r * a + s * cmTheta b d) : p = r ∧ q = s := by
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [cmTheta] at him hre
  have hqs : q = s := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by omega)
  subst hqs
  refine ⟨?_, rfl⟩
  have h3 : p * a = r * a := by linarith
  exact mul_right_cancel₀ ha'.ne' h3

theorem rep_prim_pair (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) :
    ∃ xt : m → ℂ, xt ∈ Λ ∧ (∀ j ∈ T, xt j = 0) ∧ ∃ yv : m → ℂ, yv ∈ Λ ∧ ∃ c₂ : ℤ,
      (stdH (cmL a b d ha hd lam hlam) m xt yv).im = c₂ ∧ ¬ (l : ℤ) ∣ c₂ := by
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set f := fvec a b d lam x y i₀ with hfdef
  have hfstd : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  unfold relIdx at h1 h2
  set Df := (Λ.relIndex (stdLat L m)).factorial with hDf
  set Nf := ((stdLat L m).relIndex Λ).factorial with hNf
  have hDfΛ : Df • f ∈ Λ :=
    (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h2 hfstd
      (fun j hj hle => Nat.dvd_factorial hj hle)).1
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlam0 := hlam

  set P : ℕ → Prop := fun j => ((l : ℂ) ^ j)⁻¹ • (Df • f) ∈ Λ with hPdef
  have hex : ∃ j, ¬ P j := by
    by_contra hall
    push_neg at hall
    set K : ℕ := Nf * Df with hK
    have hK0 : K ≠ 0 := Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
    have hdvd : ∀ j : ℕ, (l : ℤ) ^ j ∣ K * x ∧ (l : ℤ) ^ j ∣ K * y := by
      intro j
      have hmem : Nf • (((l : ℂ) ^ j)⁻¹ • (Df • f)) ∈ stdLat L m :=
        (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd h1 (hall j)
          (fun j hj hle => Nat.dvd_factorial hj hle)).1
      obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp (hmem i₀ (Set.mem_univ i₀))
      rw [rep_omega1, rep_omega2] at hpq
      simp only [hfdef, fvec, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, smul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hpq
      have hlj : ((l : ℂ) ^ j) ≠ 0 := pow_ne_zero _ hl0
      have e : ((p : ℝ) : ℂ) * a + ((q : ℝ) : ℂ) * cmTheta b d =
          (((K * x : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * a + (((K * y : ℤ) / (l : ℝ) ^ j : ℝ) : ℂ) * cmTheta b d := by
        apply mul_left_cancel₀ hlam
        push_cast
        rw [hK]; push_cast
        linear_combination hpq
      obtain ⟨ep, eq'⟩ := rep_coord a ha b d hd _ _ _ _ e
      have hlj' : ((l : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
      refine ⟨⟨p, ?_⟩, ⟨q, ?_⟩⟩
      · rw [eq_div_iff hlj'] at ep
        have : ((K * x : ℤ) : ℝ) = ((l ^ j * p : ℤ) : ℝ) := by push_cast at ep ⊢; linear_combination -ep
        exact_mod_cast this
      · rw [eq_div_iff hlj'] at eq'
        have : ((K * y : ℤ) : ℝ) = ((l ^ j * q : ℤ) : ℝ) := by push_cast at eq' ⊢; linear_combination -eq'
        exact_mod_cast this
    set J := K * (x.natAbs + y.natAbs) + 1
    have hJ : K * (x.natAbs + y.natAbs) < l ^ J :=
      lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.lt_pow_self hl.one_lt).le)
    have hx0 : K * x = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).1
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * x.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ < l ^ J := hJ
    have hy0 : K * y = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd J).2
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp only [Int.natAbs_natCast]
      calc K * y.natAbs ≤ K * (x.natAbs + y.natAbs) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
        _ < l ^ J := hJ
    have hK0' : (K : ℤ) ≠ 0 := by exact_mod_cast hK0
    have hx : x = 0 := (mul_eq_zero.mp hx0).resolve_left hK0'
    have hy : y = 0 := (mul_eq_zero.mp hy0).resolve_left hK0'
    apply hQ; rw [hx, hy]; simp
  classical
  set j₁ := Nat.find hex with hj₁
  have hP0 : P 0 := by simp only [hPdef, pow_zero, inv_one, one_smul]; exact hDfΛ
  have hj₁0 : j₁ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj₁, h0] at this
    exact this hP0
  have hPprev : P (j₁ - 1) := by
    have := Nat.find_min hex (show j₁ - 1 < Nat.find hex by omega)
    simpa using this
  have hPj : ¬ P j₁ := Nat.find_spec hex
  set xt := ((l : ℂ) ^ (j₁ - 1))⁻¹ • (Df • f) with hxt
  have hxtΛ : xt ∈ Λ := hPprev
  have hxtT : ∀ j ∈ T, xt j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := by rintro rfl; exact hi₀ hj
    simp [hxt, hfdef, fvec, Pi.single_apply, hne]
  have hdiv : ((l : ℂ)⁻¹) • xt ∉ Λ := by
    rw [hxt, smul_smul, ← mul_inv, ← pow_succ', show j₁ - 1 + 1 = j₁ by omega]
    exact hPj
  refine ⟨xt, hxtΛ, hxtT, ?_⟩
  have hnd : ¬ ∀ yv ∈ Λ, ∃ k : ℤ, altE (stdH L m) ((l : ℂ)⁻¹ • xt) yv = k := by
    intro hall
    apply hdiv
    have : ((l : ℂ)⁻¹ • xt) ∈ dualLat (stdH L m) Λ := hall
    rw [hΛ] at this
    exact this
  push_neg at hnd
  obtain ⟨yv, hyv, hyk⟩ := hnd
  have hxtd : xt ∈ dualLat (stdH L m) Λ := by rw [hΛ]; exact hxtΛ
  obtain ⟨c₂, hc₂⟩ := hxtd yv hyv
  refine ⟨yv, hyv, c₂, hc₂, ?_⟩
  rintro ⟨t, rfl⟩
  apply hyk t
  simp only [altE] at hc₂ ⊢
  have e : (stdH L m ((l : ℂ)⁻¹ • xt) yv) = (((l : ℝ)⁻¹ : ℝ) : ℂ) * stdH L m xt yv := by
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
  rw [e, Complex.im_ofReal_mul, hc₂]
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  push_cast
  field_simp

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SatStdOfAll
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma altE_single (L : PeriodPair) (v : m → ℂ) (n : ℕ) (j : m) (w : ℂ) :
    altE (stdH L m) v (n • Pi.single j w) = (n : ℝ) * (v j * conj w).im / area L := by
  classical
  unfold altE
  rw [stdH_apply]
  have hs : (∑ i, v i * conj ((n • Pi.single j w : m → ℂ) i)) = (n : ℂ) * (v j * conj w) := by
    rw [Finset.sum_eq_single j]
    · simp [nsmul_eq_mul]
      ring
    · intro i _ hi
      simp [hi]
    · simp
  rw [hs, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, div_eq_mul_inv]

lemma alpha_eq (x y : ℤ) :
    lam * ((x * a : ℂ) + y * cmTheta b d) =
      (x : ℝ) • (cmL a b d ha hd lam hlam).ω₁ + (y : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma theta_alpha_eq (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) :
    cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)) =
      ((-y * c : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₁ +
        ((x * a + y * b : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  linear_combination (-(lam * y)) * hn

lemma coord_mem (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) (n : ℕ) (w : ℂ)
    (h1 : ∃ k : ℤ, (n : ℝ) * (w * conj (lam * ((x * a : ℂ) + y * cmTheta b d))).im
      / area (cmL a b d ha hd lam hlam) = k)
    (h2 : ∃ k : ℤ, (n : ℝ) * (w * conj (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)))).im
      / area (cmL a b d ha hd lam hlam) = k) :
    ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w ∈ (cmL a b d ha hd lam hlam).lattice := by
  set L := cmL a b d ha hd lam hlam with hL
  obtain ⟨s, t, hz⟩ := coords L ((n : ℂ) * w)
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hnim : ∀ u : ℂ, (n : ℝ) * (w * u).im = (((n : ℂ) * w) * u).im := by
    intro u
    rw [mul_assoc]
    simp [Complex.mul_im]
  rw [hnim, hz, alpha_eq (ha := ha) (hd := hd) (hlam := hlam), im_mul_conj] at hk1
  rw [hnim, hz, theta_alpha_eq (ha := ha) (hd := hd) (hlam := hlam) hn, im_mul_conj] at hk2
  obtain ⟨j1, hj1⟩ := int_of_div L hk1
  obtain ⟨j2, hj2⟩ := int_of_div L hk2
  push_cast at hj1 hj2
  have hQs : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * s = ((-(y * c * j1 + x * j2) : ℤ) : ℝ) := by
    push_cast
    linear_combination (-((y : ℝ) * c)) * hj1 + (-(x : ℝ)) * hj2
  have hQt : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * t =
      (((x * a + y * b) * j1 - y * j2 : ℤ) : ℝ) := by
    push_cast
    linear_combination ((x : ℝ) * a + y * b) * hj1 + (-(y : ℝ)) * hj2
  rw [show ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w =
      ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) * ((n : ℂ) * w) by push_cast; ring, hz]
  refine (lattice_iff L _).mpr ⟨-(y * c * j1 + x * j2), (x * a + y * b) * j1 - y * j2, ?_⟩
  have cs := congrArg (fun r : ℝ => (r : ℂ)) hQs
  have ct := congrArg (fun r : ℝ => (r : ℂ)) hQt
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast] at cs ct
  simp only [Complex.real_smul, Complex.ofReal_intCast]
  linear_combination L.ω₁ * cs + L.ω₂ * ct

lemma sat_std_of_all (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) (x y : ℤ)
    (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (Λ : AddSubgroup (m → ℂ))
    (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ v ∈ Λ, cmTheta b d • v ∈ Λ)
    (hall : ∀ j, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) :
    ∃ n : ℕ, ¬ l ∣ n ∧ ∀ v ∈ Λ, n • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  have hn := theta_norm hok.1
  have hall' : ∀ j, ∃ N : ℕ, ¬ l ∣ N ∧
      N • (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) ∈ Λ := hall
  choose N hNl hNmem using hall'
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  refine ⟨Q.natAbs * Q.natAbs * ∏ j, N j, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hl).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hl).mp h with h' | h' <;> exact hQ (Int.natCast_dvd.mpr h')
    · obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp h
      exact hNl j hj
  · intro v hv
    have hvd : v ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by
      rw [hsd]
      exact hv
    rw [mem_dualLat_iff] at hvd
    rw [mem_stdLat_iff]
    intro i
    have e1 := hvd _ (hNmem i)
    have e2 := hvd _ (hθ _ (hNmem i))
    have hsm : cmTheta b d • (N i • Pi.single i (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) =
        N i • Pi.single i (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [nsmul_eq_mul]
        ring
      · simp [hk]
    rw [altE_single] at e1
    rw [hsm, altE_single] at e2
    have hm := coord_mem hn x y (N i) (v i) e1 e2
    have hmem : ((N i : ℤ) * Q) • v i ∈ (cmL a b d ha hd lam hlam).lattice := by
      rw [zsmul_eq_mul]
      exact_mod_cast hm
    have hnZ : ((Q.natAbs * Q.natAbs * ∏ j, N j : ℕ) : ℤ) =
        (Q * ∏ j ∈ Finset.univ.erase i, (N j : ℤ)) * ((N i : ℤ) * Q) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      push_cast
      rw [abs_mul_abs_self]
      ring
    rw [Pi.smul_apply, ← natCast_zsmul, hnZ, mul_smul]
    exact Submodule.smul_mem _ _ hmem

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

