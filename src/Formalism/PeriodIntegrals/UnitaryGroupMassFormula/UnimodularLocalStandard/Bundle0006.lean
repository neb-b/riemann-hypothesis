module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSelfInt

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsGoodForm
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Transport
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma mem_dualLat_iff (H : Sesq V) (Λ : AddSubgroup V) (x : V) :
    x ∈ dualLat H Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, altE H x y = k := by
  exact Iff.rfl

lemma mem_imgLat_iff (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (x : V) :
    x ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [imgLat, AddSubgroup.mem_map]

lemma selfDual_img (H : Sesq V) (g : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) {Λ : AddSubgroup V}
    (hΛ : IsSelfDual H Λ) : IsSelfDual H (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  have hg' : ∀ a b, H (g a) (g b) = H a b := fun a b => by simpa using hg a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  rw [mem_dualLat_iff, mem_imgLat_iff]
  obtain ⟨x₀, rfl⟩ := g.surjective x
  have key : (∀ y ∈ imgLat (g : V →ₗ[ℂ] V) Λ, ∃ k : ℤ, altE H (g x₀) y = k) ↔ x₀ ∈ dualLat H Λ := by
    rw [mem_dualLat_iff]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (g y) ((mem_imgLat_iff g Λ _).mpr ⟨y, hy, rfl⟩)
      exact ⟨k, by rw [← hk]; simp only [altE]; rw [hg']⟩
    · intro h y' hy'
      obtain ⟨y, hy, rfl⟩ := (mem_imgLat_iff g Λ y').mp hy'
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨k, by simp only [altE]; rw [hg']; exact hk⟩
  rw [key, hΛ]
  constructor
  · intro h
    exact ⟨x₀, h, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [g.injective hxy] at hy

lemma comm_img (g : V ≃ₗ[ℂ] V) {S Λ : AddSubgroup V}
    (hg1 : relIdx S (imgLat (g : V →ₗ[ℂ] V) S) ≠ 0) (hg2 : relIdx (imgLat (g : V →ₗ[ℂ] V) S) S ≠ 0)
    (h1 : relIdx S Λ ≠ 0) (h2 : relIdx Λ S ≠ 0) :
    relIdx S (imgLat (g : V →ₗ[ℂ] V) Λ) ≠ 0 ∧ relIdx (imgLat (g : V →ₗ[ℂ] V) Λ) S ≠ 0 := by
  have hinj : Function.Injective (g : V →ₗ[ℂ] V).toAddMonoidHom := g.injective
  have hm : ∀ A B : AddSubgroup V, relIdx (imgLat (g : V →ₗ[ℂ] V) A) (imgLat (g : V →ₗ[ℂ] V) B) = relIdx A B :=
    fun A B => AddSubgroup.relIndex_map_map_of_injective A B hinj
  refine ⟨?_, ?_⟩
  · exact AddSubgroup.relIndex_ne_zero_trans hg1 (by rw [← hm S Λ] at h1; exact h1)
  · exact AddSubgroup.relIndex_ne_zero_trans (by rw [← hm Λ S] at h2; exact h2) hg2

lemma imgLat_trans (g σ : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) :
    imgLat ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = imgLat (σ : V →ₗ[ℂ] V) (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  ext x
  simp only [mem_imgLat_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma isom_trans (H : Sesq V) (g σ : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) (hσ : IsIsom H H (σ : V →ₗ[ℂ] V)) :
    IsIsom H H ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
  intro x y
  have h1 := hσ (g x) (g y)
  have h2 := hg x y
  simp only [LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, h2]

end Transport

lemma exists_good_form {a : ℕ} {b c : ℤ} {d : ℕ} (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) :
    ∃ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  obtain ⟨hE, _, _, hd⟩ := hok
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  norm_num at h1 h2 h3
  have hb : (l : ℤ) ∣ b := by
    have h4 := dvd_sub (dvd_sub h3 h1) h2
    have e : (a : ℤ) + b + c - a - c = b := by ring
    rwa [e] at h4
  have hl2 : (l : ℤ) ^ 2 ∣ (d : ℤ) := by
    have e : (d : ℤ) = 4 * a * c - b ^ 2 := by linarith
    rw [e]
    refine dvd_sub ?_ (pow_dvd_pow_of_dvd hb 2)
    rw [pow_two]
    exact mul_dvd_mul (dvd_mul_of_dvd_right h1 4) h2
  have hl2' : l ^ 2 ∣ d := by exact_mod_cast hl2
  have hld : l ∣ d := (dvd_pow_self l two_ne_zero).trans hl2'
  have hleq : l = d := (Nat.prime_dvd_prime_iff_eq hl hd).mp hld
  subst hleq
  have h5 := Nat.le_of_dvd hd.pos hl2'
  have h6 := hd.two_le
  nlinarith

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyNewton
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem keyNewton : KeyNewton := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h k hk w hw
  obtain ⟨hOK, -, hθ, -, -, hl, -, -, -⟩ := h
  obtain ⟨hwsat, hwT, p, q, hq, hww⟩ := hw
  obtain ⟨τ, r, s, hτ1, hτ2, hs, hτsat⟩ := rep_tau a b c d hOK Λ hθ hl
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
    exact_mod_cast this
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (dvd_zero _)
    exact_mod_cast this
  set ε : ℂ := ((l ^ k * p : ℤ) : ℂ) / (q : ℂ) with hε
  have hεc : conj ε = ε := by rw [hε, map_div₀, map_intCast, map_intCast]
  have hξ : (1 - ε * τ) * conj (1 - ε * τ) = 1 - ε + ε ^ 2 * ((r : ℂ) / s) := by
    rw [map_sub, map_one, map_mul, hεc]
    linear_combination (-ε) * hτ1 + ε ^ 2 * hτ2
  refine ⟨(1 - ε * τ) • w, ?_, ?_, p ^ 2 * (r * q - s * q + l ^ k * p * r), q ^ 3 * s, ?_, ?_⟩
  · have e : (1 - ε * τ) • w = w - ε • (τ • w) := by rw [sub_smul, one_smul, smul_smul]
    rw [e, hε]
    exact rep_sat_sub l Λ hl hwsat (rep_sat_rat l Λ hl (hτsat w hwsat) _ _ hq)
  · intro j hj; simp [hwT j hj]
  · intro h
    rcases hlp.dvd_mul.mp h with h | h
    · exact hq (hlp.dvd_of_dvd_pow h)
    · exact hs h
  · rw [rep_H_smul, hξ, hww]
    rw [hε]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepSingleSat
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def zT {m : Type} [DecidableEq m] (T : Finset m) (y : m → ℂ) : m → ℂ := fun i => if i ∈ T then 0 else y i

theorem rep_sat_zero {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (hl : l.Prime) : SatMem l Λ 0 :=
  ⟨1, hl.not_dvd_one, by rw [smul_zero]; exact zero_mem Λ⟩

theorem rep_sat_zsmul {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) :
    SatMem l Λ ((r : ℂ) • v) := by
  obtain ⟨n, hn, hv⟩ := hv
  refine ⟨n, hn, ?_⟩
  rw [smul_comm, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hv r

theorem rep_sat_theta {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {b : ℤ} {d : ℕ}
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {v : m → ℂ} (hv : SatMem l Λ v) : SatMem l Λ (cmTheta b d • v) := by
  obtain ⟨n, hn, hv⟩ := hv
  refine ⟨n, hn, ?_⟩
  rw [smul_comm]
  exact hθ _ hv

theorem rep_sat_elt {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (hl : l.Prime) {b : ℤ} {d : ℕ}
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {v : m → ℂ} (hv : SatMem l Λ v) (n c s : ℤ) (hs : ¬ (l : ℤ) ∣ s) :
    SatMem l Λ ((((n : ℂ) - c * conj (cmTheta b d)) / s) • v) := by
  have hconj : conj (cmTheta b d) = b - cmTheta b d := by
    unfold cmTheta
    simp only [map_div₀, map_add (f := _), map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have e : (((n : ℂ) - c * conj (cmTheta b d)) / s) • v =
      (((n - c * b : ℤ) : ℂ) / s) • v + ((c : ℂ) / s) • (cmTheta b d • v) := by
    rw [hconj, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  rw [e]
  exact rep_sat_add (l := l) (Λ := Λ) hl (rep_sat_rat (l := l) (Λ := Λ) hl hv _ s hs) (rep_sat_rat (l := l) (Λ := Λ) hl (rep_sat_theta l Λ hθ hv) c s hs)

section Zero

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

theorem rep_single_sat (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (j : m)
    (hj : SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (Pi.single j (z j)) := by
  obtain ⟨hc4, -, -, -⟩ := hOK
  set θ := cmTheta b d with hθdef
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have hθre : θ.re = b / 2 := by simp [hθdef, cmTheta]
  have hθim : θ.im = Real.sqrt d / 2 := by simp [hθdef, cmTheta]
  have hconj : conj θ = b - θ := by
    apply Complex.ext <;> simp [hθre, hθim] <;> ring
  set α : ℂ := (x * a : ℂ) + y * θ with hαdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef

  have hαn : Complex.normSq α = a * Q := by
    rw [Complex.normSq_apply]
    have hre : α.re = x * a + y * (b / 2) := by simp [hαdef, hθre]
    have him : α.im = y * (Real.sqrt d / 2) := by simp [hαdef, hθim]
    rw [hre, him, hQdef]
    have hc4' : (b : ℝ) ^ 2 + d = 4 * a * c := by exact_mod_cast hc4.symm
    push_cast
    linear_combination (y ^ 2 / 4) * hsq + (y ^ 2 / 4) * hc4'
  have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h]; exact dvd_zero _)
  have hQ0' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hα0 : α ≠ 0 := by
    intro h
    have h1 := hαn
    rw [h, map_zero] at h1
    have h2 : (a : ℝ) * Q ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hQ0)
    exact h2 h1.symm
  have hnl : Complex.normSq lam ≠ 0 := (Complex.normSq_pos.2 hlam).ne'
  have harea : area (cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have e : conj (lam * (a : ℂ)) * (lam * θ) = ((Complex.normSq lam * a : ℝ) : ℂ) * θ := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    show |(conj (lam * (a : ℂ)) * (lam * θ)).im| = _
    rw [e, Complex.im_ofReal_mul, hθim]
    exact abs_of_pos (by have := Complex.normSq_pos.2 hlam; positivity)

  have hHs : ∀ u : ℂ, stdH (cmL a b d ha hd lam hlam) m z (Pi.single j u) =
      z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj u := by
    intro u
    simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
    · simp [Matrix.smul_apply]
    · intro j' _ hj'
      simp [Pi.single_apply, hj']
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j' _ => ?_
      by_cases hj' : j' = j
      · subst hj'
        simp [Matrix.smul_apply, Matrix.one_apply_ne hi]
      · simp [Pi.single_apply, hj']
    · simp
  obtain ⟨N, hN, hw⟩ := hj
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hz' : z ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by rw [hΛ]; exact hz
  have hwe : (N • Pi.single j (lam * α) : m → ℂ) = Pi.single j ((N : ℂ) * (lam * α)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [nsmul_eq_mul]
    · simp [Pi.single_apply, hi]
  have hθw : θ • Pi.single j ((N : ℂ) * (lam * α)) = Pi.single j (θ * ((N : ℂ) * (lam * α))) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Pi.single_apply, hi]
  obtain ⟨m1, hm1⟩ := hz' _ hw
  obtain ⟨m2, hm2⟩ := hz' _ (hθ _ hw)
  simp only [altE] at hm1 hm2
  rw [hwe] at hm1 hm2
  rw [hθw, hHs] at hm2
  rw [hHs] at hm1
  set X := z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) with hXdef
  have hm2' : X.re * (-(Real.sqrt d / 2)) + X.im * (b / 2) = m2 := by
    have e : (X * conj θ).im = m2 := by
      rw [← hm2, hXdef, map_mul (starRingEnd ℂ) θ]
      congr 1
      ring
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hθre, hθim] at e
    linarith
  rw [hm1] at hm2'
  have hX : X * (Real.sqrt d : ℂ) = 2 * ((m1 : ℂ) * θ - m2) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero,
        sub_zero, zero_mul, Complex.mul_im, Complex.sub_im]
      linarith
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.sub_re,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero,
        zero_mul, add_zero, sub_zero, Complex.mul_re, hm1]
      ring

  have hcl : conj lam = (Complex.normSq lam : ℂ) / lam := by
    rw [eq_div_iff hlam, mul_comm, Complex.mul_conj]
  have hca : conj α = (Complex.normSq α : ℂ) / α := by
    rw [eq_div_iff hα0, mul_comm, Complex.mul_conj]
  have hsdC : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hnlC : (Complex.normSq lam : ℂ) ≠ 0 := by exact_mod_cast hnl
  have hzj : z j = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) * (lam * α) := by
    have hareaC : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
      rw [harea]
      push_cast
      exact mul_ne_zero (mul_ne_zero hnlC ha0) (div_ne_zero hsdC two_ne_zero)
    have hK : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) *
        (Real.sqrt d : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (inv_ne_zero hareaC)
        ((map_ne_zero _).2 (mul_ne_zero hN0' (mul_ne_zero hlam hα0)))) hsdC
    apply mul_right_cancel₀ hK
    calc z j * (((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) *
          (Real.sqrt d : ℂ)) = X * (Real.sqrt d : ℂ) := by rw [hXdef]; ring
      _ = 2 * ((m1 : ℂ) * θ - m2) := hX
      _ = _ := by
          rw [harea, map_mul, map_mul, map_natCast, hcl, hca, hαn, hconj]
          push_cast
          field_simp
          ring
  have hsing : Pi.single j (z j) = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) •
      Pi.single j (lam * α) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [hzj]
    · simp [Pi.single_apply, hi]
  have hs : ¬ (l : ℤ) ∣ (N * Q : ℤ) := by
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    intro h
    rcases hp.dvd_or_dvd h with h1 | h1
    · exact hN (Int.natCast_dvd_natCast.1 h1)
    · exact hQ h1
  rw [hsing]
  exact rep_sat_elt l Λ hl hθ ⟨N, hN, hw⟩ (m1 * b - m2) m1 (N * Q) hs

theorem rep_zT_sat (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m)
    (hT : ∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (zT T z) := by
  have hsum : SatMem l Λ (∑ j ∈ T, Pi.single j (z j)) :=
    Finset.sum_induction _ (SatMem l Λ) (fun _ _ h1 h2 => rep_sat_add (l := l) (Λ := Λ) hl h1 h2) (rep_sat_zero l Λ hl)
      (fun j hj => rep_single_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ j (hT j hj) hz)
  have e : zT T z = z - ∑ j ∈ T, Pi.single j (z j) := by
    funext i
    simp only [zT, Pi.sub_apply, Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  rw [e]
  exact rep_sat_sub (l := l) (Λ := Λ) hl (rep_sat_of_mem (l := l) (Λ := Λ) hz hl) hsum

theorem rep_H_zT (T : Finset m) {z y : m → ℂ} (hz : ∀ j ∈ T, z j = 0) :
    stdH (cmL a b d ha hd lam hlam) m z (zT T y) = stdH (cmL a b d ha hd lam hlam) m z y := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold zT
  by_cases hj : j ∈ T
  · rw [if_pos hj, map_zero, mul_zero]
    by_cases hij : i = j
    · subst hij
      rw [hz i hj, zero_mul, zero_mul]
    · rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, mul_zero, zero_mul]
  · rw [if_neg hj]

end Zero

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

