module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRepModl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RamDef
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def UnitVecRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m]
    [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (x0 y0 : ℤ) (T : Finset m) (i₀ : m),
    KeyHyps a b c d ha hd lam hlam m Λ d x0 y0 T i₀ →
    ∀ x : m → ℂ, SatMem d Λ x → (∀ j ∈ T, x j = 0) →
      (x = 0 ∨ ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m x x = repKappa a b d ha hd lam hlam * p / q) →
    ∀ z₀ : m → ℂ, SatMem d Λ z₀ → (∀ j ∈ T, z₀ j = 0) → stdH (cmL a b d ha hd lam hlam) m z₀ x = 0 → z₀ ≠ 0 →
    ∃ y : m → ℂ, SatMem d Λ y ∧ (∀ j ∈ T, y j = 0) ∧ stdH (cmL a b d ha hd lam hlam) m y x = 0 ∧
      ∃ p q : ℤ, ¬ (d : ℤ) ∣ p ∧ ¬ (d : ℤ) ∣ q ∧
        stdH (cmL a b d ha hd lam hlam) m y y = repKappa a b d ha hd lam hlam * p / q

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSmulRight
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem rep_H_add_self (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (u v : m → ℂ) :
    stdH L m (u + v) (u + v) = stdH L m u u + stdH L m u v + stdH L m v u + stdH L m v v := by
  first
  | (simp only [map_add (f := _), LinearMap.add_apply]; ring)
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.add_apply, map_add (f := _), add_mul, mul_add,
      Finset.sum_add_distrib]; ring)

theorem rep_H_smul_left (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m (ξ • u) v = ξ * stdH L m u v := by
  first
  | (simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])

theorem rep_H_smul_right (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (u v : m → ℂ) :
    stdH L m v (ξ • u) = conj ξ * stdH L m v u := by
  first
  | (simp only [LinearMap.map_smulₛₗ, smul_eq_mul])
  | (simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum];
     refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring)

theorem rep_unit_vec (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m) (h : KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀) (hld : ¬ (l : ℤ) ∣ d) :
    ∃ w : m → ℂ, SatMem l Λ w ∧ (∀ j ∈ T, w j = 0) ∧ ∃ N S : ℤ, ¬ (l : ℤ) ∣ N ∧ ¬ (l : ℤ) ∣ S ∧
      stdH (cmL a b d ha hd lam hlam) m w w = repKappa a b d ha hd lam hlam * ((N : ℂ) / S) := by
  obtain ⟨xt, hxt, hxtT, yv, hyv, c₂, hc₂, hc₂l⟩ := rep_prim_pair a b c d ha hd lam hlam m Λ l x y T i₀ h
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := h
  set L := cmL a b d ha hd lam hlam with hL
  set H := stdH L m with hHdef
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = repKappa a b d ha hd lam hlam := ⟨_, rfl⟩
  rw [← hκdef]
  set θ := cmTheta b d with hθdef
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  obtain ⟨mm, c₂', hmc, hc₂'⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hxt hyv
  rw [← hκdef] at hmc
  have hcc : c₂' = c₂ := by
    have : (c₂' : ℝ) = c₂ := by rw [← hc₂', hc₂]
    exact_mod_cast this
  rw [hcc] at hmc
  obtain ⟨m1, hm1⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hxt
  rw [← hκdef] at hm1
  have hy'sat := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ T hT hyv
  set yz := zT T yv with hyz
  have hyzT : ∀ j ∈ T, yz j = 0 := by intro j hj; simp [hyz, zT, hj]
  obtain ⟨n', hn', hn'y⟩ := hy'sat
  obtain ⟨m2, hm2⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hn'y
  rw [rep_H_nsmul, ← hκdef] at hm2
  have hn'0 : (n' : ℂ) ≠ 0 := by
    have : n' ≠ 0 := by rintro rfl; exact hn' (dvd_zero _)
    exact_mod_cast this
  have hS : ¬ (l : ℤ) ∣ (n' : ℤ) ^ 2 := fun h => hn' (by exact_mod_cast hlp.dvd_of_dvd_pow h)
  have hyy : H yz yz = κ * ((m2 : ℂ) / ((n' : ℤ) ^ 2 : ℤ)) := by
    push_cast; field_simp; linear_combination hm2
  have hκc : conj κ = κ := by
    rw [hκdef, rep_kappa_eq a b d ha hd lam hlam, map_div₀, Complex.conj_ofReal, map_ofNat]
  have hxy : H xt yz = κ * ((mm : ℂ) - c₂ * conj θ) := by rw [hHdef, rep_H_zT a b d ha hd lam hlam m T hxtT]; exact hmc
  have hyx : H yz xt = κ * ((mm : ℂ) - c₂ * θ) := by
    rw [hHdef, ← rep_H_conj, ← hHdef, hxy, map_mul, hκc, map_sub, map_mul, map_intCast, map_intCast,
      Complex.conj_conj]
  have e1 := rep_theta_add_conj b d
  have e2 := rep_theta_mul_conj a b c d hOK.1

  by_cases k1 : (l : ℤ) ∣ m1
  swap
  · refine ⟨xt, rep_sat_of_mem l Λ hxt hl, hxtT, m1 * n' ^ 2, n' ^ 2, ?_, hS, ?_⟩
    · intro hh; rcases hlp.dvd_mul.mp hh with hh | hh
      · exact k1 hh
      · exact hS hh
    · rw [hm1]; push_cast; field_simp
  by_cases k2 : (l : ℤ) ∣ m2
  swap
  · exact ⟨yz, ⟨n', hn', hn'y⟩, hyzT, m2, n' ^ 2, k2, hS, hyy⟩
  by_cases k3 : (l : ℤ) ∣ (m1 + 2 * mm - c₂ * b) * n' ^ 2 + m2
  swap
  · refine ⟨xt + yz, rep_sat_add l Λ hl (rep_sat_of_mem l Λ hxt hl) ⟨n', hn', hn'y⟩, ?_, _, n' ^ 2, k3, hS, ?_⟩
    · intro j hj; simp [hxtT j hj, hyzT j hj]
    · rw [rep_H_add_self, hm1, hxy, hyx, hyy]
      push_cast; field_simp
      linear_combination (-κ * c₂ * (n' : ℂ) ^ 2) * e1
  by_cases k4 : (l : ℤ) ∣ (a * c * m1 + mm * b - 2 * a * c * c₂) * n' ^ 2 + m2
  swap
  · refine ⟨θ • xt + yz, rep_sat_add l Λ hl (rep_sat_theta l Λ hθ (rep_sat_of_mem l Λ hxt hl)) ⟨n', hn', hn'y⟩,
      ?_, _, n' ^ 2, k4, hS, ?_⟩
    · intro j hj; simp [hxtT j hj, hyzT j hj]
    · rw [rep_H_add_self, rep_H_smul, rep_H_smul_left, rep_H_smul_right, hm1, hxy, hyx, hyy]
      push_cast; field_simp
      linear_combination (κ * (n' : ℂ) ^ 2 * m1) * e2 + (κ * (n' : ℂ) ^ 2 * mm) * e1 -
        (2 * κ * (n' : ℂ) ^ 2 * c₂) * e2
  exfalso
  have d3 : (l : ℤ) ∣ (2 * mm - c₂ * b) * n' ^ 2 := by
    have e : (2 * mm - c₂ * b) * (n' : ℤ) ^ 2 = ((m1 + 2 * mm - c₂ * b) * n' ^ 2 + m2) - m1 * n' ^ 2 - m2 := by ring
    rw [e]; exact dvd_sub (dvd_sub k3 (Dvd.dvd.mul_right k1 _)) k2
  have d4 : (l : ℤ) ∣ (mm * b - 2 * a * c * c₂) * n' ^ 2 := by
    have e : (mm * b - 2 * a * c * c₂) * (n' : ℤ) ^ 2 =
        ((a * c * m1 + mm * b - 2 * a * c * c₂) * n' ^ 2 + m2) - (a * c) * m1 * n' ^ 2 - m2 := by ring
    rw [e]; exact dvd_sub (dvd_sub k4 (Dvd.dvd.mul_right (Dvd.dvd.mul_left k1 _) _)) k2
  have d3' : (l : ℤ) ∣ 2 * mm - c₂ * b := (hlp.dvd_mul.mp d3).resolve_right hS
  have d4' : (l : ℤ) ∣ mm * b - 2 * a * c * c₂ := (hlp.dvd_mul.mp d4).resolve_right hS
  have d5 : (l : ℤ) ∣ c₂ * d := by
    have e : c₂ * (d : ℤ) = b * (2 * mm - c₂ * b) - 2 * (mm * b - 2 * a * c * c₂) := by
      linear_combination (-c₂) * hOK.1
    rw [e]; exact dvd_sub (Dvd.dvd.mul_left d3' b) (Dvd.dvd.mul_left d4' 2)
  rcases hlp.dvd_mul.mp d5 with h5 | h5
  · exact hc₂l h5
  · exact hld h5

theorem keyStart_of_ram (hR : KeyStartRam) : KeyStart := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h
  by_cases hld : l = d
  · exact hR a b c d ha hd lam hlam m Λ l x y T i₀ h hld
  have hOK := h.1
  have hl := h.2.2.2.2.2.1
  have hQ := h.2.2.2.2.2.2.1
  have hθ := h.2.2.1
  have hld' : ¬ (l : ℤ) ∣ d := by
    intro hh
    have : l ∣ d := by exact_mod_cast hh
    exact hld ((Nat.prime_dvd_prime_iff_eq hl hOK.2.2.2).mp this)
  obtain ⟨w, hw, hwT, N, S, hN, hS, hH⟩ := rep_unit_vec a b c d ha hd lam hlam m Λ l x y T i₀ h hld'
  obtain ⟨s, t, p, hp⟩ := rep_rep_modl hl a b c d hOK.1 hld' N S _ hN hS hQ
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  refine ⟨((s : ℂ) + t * cmTheta b d) • w, ?_, ?_, p, (a * x ^ 2 + b * x * y + c * y ^ 2) * S, ?_, ?_⟩
  · rw [add_smul, ← smul_smul]
    exact rep_sat_add l Λ hl (rep_sat_zsmul l Λ hw s) (rep_sat_zsmul l Λ (rep_sat_theta l Λ hθ hw) t)
  · intro j hj; simp [hwT j hj]
  · intro hh; rcases hlp.dvd_mul.mp hh with hh | hh
    · exact hQ hh
    · exact hS hh
  · have hS0 : (S : ℂ) ≠ 0 := by
      have : S ≠ 0 := by rintro rfl; exact hS (dvd_zero _)
      exact_mod_cast this
    obtain ⟨Q0, hQ0def⟩ : ∃ Q0 : ℤ, Q0 = a * x ^ 2 + b * x * y + c * y ^ 2 := ⟨_, rfl⟩
    rw [← hQ0def] at hp hQ ⊢
    have hQ0 : (Q0 : ℂ) ≠ 0 := by
      have : Q0 ≠ 0 := by rintro rfl; exact hQ (dvd_zero _)
      exact_mod_cast this
    have hf' : stdH (cmL a b d ha hd lam hlam) m (fvec a b d lam x y i₀) (fvec a b d lam x y i₀) =
        repKappa a b d ha hd lam hlam * (Q0 : ℂ) := by
      rw [rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀, hQ0def]
    have e1 := rep_theta_add_conj b d
    have e2 := rep_theta_mul_conj a b c d hOK.1
    have hX : ((s : ℂ) + t * cmTheta b d) * conj ((s : ℂ) + t * cmTheta b d) =
        ((s ^ 2 + b * s * t + a * c * t ^ 2 : ℤ) : ℂ) := by
      simp only [map_add (f := _), map_mul, map_intCast]; push_cast
      linear_combination ((s : ℂ) * t) * e1 + (t : ℂ) ^ 2 * e2
    have hpC : (l : ℂ) ^ 1 * (p : ℂ) = ((s ^ 2 + b * s * t + a * c * t ^ 2 : ℤ) : ℂ) * N - (Q0 : ℂ) * S := by
      rw [pow_one]; exact_mod_cast hp.symm
    rw [rep_H_smul, hX, hH, hf', hpC]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.StdHSingleZero
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma stdH_symm (L : PeriodPair) (x y : m → ℂ) : stdH L m y x = conj (stdH L m x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [stdH_apply, stdH_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma stdH_single_zero (L : PeriodPair) (j : m) (w : ℂ) {z : m → ℂ} (hz : z j = 0) :
    stdH L m (Pi.single j w) z = 0 := by
  rw [stdH_apply]
  have hsum : ∑ i, (Pi.single j w : m → ℂ) i * conj (z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = j
    · subst h
      rw [hz, map_zero, mul_zero]
    · simp [h]
  rw [hsum, zero_mul]

private theorem stdH_sub_eq_and_add_conj_eq_of_stdH_eq (L : PeriodPair) (v f' : m → ℂ)
    (hvv : PI.ULS.stdH L m v v = PI.ULS.stdH L m f' f') :
    PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' ∧
      PI.ULS.stdH L m v (v - f') + conj (PI.ULS.stdH L m v (v - f')) =
        PI.ULS.stdH L m (v - f') (v - f') := by
  have h1 : PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' :=
    map_sub (PI.ULS.stdH L m v) v f'
  refine ⟨h1, ?_⟩
  have h2 : PI.ULS.stdH L m (v - f') (v - f') =
      PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' - (PI.ULS.stdH L m f' v - PI.ULS.stdH L m f' f') := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [h1, h2, map_sub, ← stdH_symm L v f', ← stdH_symm L v v, hvv]
  ring

private theorem isKv_sub_stdH_smul {L : PeriodPair} {e : ℤ}
    (hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = (e : ℂ)) (hl0 : lam ≠ 0) {z w : m → ℂ} {t : ℂ}
    (ht : IsK b d t) (hz : IsKv b d lam z) (hw : IsKv b d lam w) :
    IsKv b d lam (w - ((kappa L lam * t)⁻¹ * PI.ULS.stdH L m w z) • z) := by
  obtain ⟨s, hs, hH⟩ := isK_H hn L hl0 hw hz
  rw [hH, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ (kappa_ne L hl0)]
  exact isKv_sub hw (isKv_smul hn (isK_mul hn (isK_inv hn ht) hs) hz)

lemma qrefl_to (hok : CmOK a b c d) (v f' : m → ℂ)
    (hvv : stdH (cmL a b d ha hd lam hlam) m v v = stdH (cmL a b d ha hd lam hlam) m f' f')
    (hne : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v f' ≠ 0)
    (hvK : IsKv b d lam v) (hfK : IsKv b d lam f') :
    ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      σ v = f' ∧ ∀ w, stdH (cmL a b d ha hd lam hlam) m w (v - f') = 0 → σ w = w := by
  obtain ⟨hvz, hκ⟩ := stdH_sub_eq_and_add_conj_eq_of_stdH_eq (PI.ULS.cmL a b d ha hd lam hlam) v f' hvv
  have hκ0 : PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f') ≠ 0 := by
    rw [hvz]; exact hne
  have hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = ((a * c : ℤ) : ℂ) := by
    rw [theta_norm hok.1]; push_cast; ring
  have hzK : IsKv b d lam (v - f') := isKv_sub hvK hfK
  obtain ⟨t, ht, htF⟩ := isK_H hn (PI.ULS.cmL a b d ha hd lam hlam) hlam hvK hzK
  have htF' : conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')) =
      kappa (PI.ULS.cmL a b d ha hd lam hlam) lam * conj t := by
    rw [htF, map_mul, kappa_conj]
  obtain ⟨σ, hσ⟩ : ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      σ = qequiv (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m) (v - f') hκ0 hκ := ⟨_, rfl⟩
  have hσapp : ∀ x, σ x = x - ((PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f'))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, qequiv_apply]
  have hσsymm : ∀ x, σ.symm x = x - ((conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, ← qmap_apply]; rfl
  have hs1 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega1, mul_div_cancel_left₀ _ hlam]
      exact_mod_cast isK_int (b := b) (d := d) (a : ℤ)) i
  have hs2 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega2, mul_div_cancel_left₀ _ hlam]
      exact isK_theta) i
  have hφ : ∀ x, IsKv b d lam x → IsKv b d lam ((σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσapp, htF]
    exact isKv_sub_stdH_smul hn hlam ht hzK hx
  have hψ : ∀ x, IsKv b d lam x →
      IsKv b d lam ((σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσsymm, htF']
    exact isKv_sub_stdH_smul hn hlam (isK_conj ht) hzK hx
  obtain ⟨N, hN, hN1⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hφ _ (hs1 i)) (fun i => hφ _ (hs2 i))
  obtain ⟨N', hN', hN2⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hψ _ (hs1 i)) (fun i => hψ _ (hs2 i))
  have hidx := comm_of_bounded σ hN hN' (fun s hs => hN1 s hs) (fun s hs => hN2 s hs)
  refine ⟨σ, ?_, hidx.1, hidx.2, ?_, ?_⟩
  · rw [hσ]
    exact qequiv_isom _ (fun x y => stdH_symm _ x y) _ hκ0 hκ
  · rw [hσapp, inv_mul_cancel₀ hκ0, one_smul, sub_sub_cancel]
  · intro w hw
    rw [hσapp, hw, mul_zero, zero_smul, sub_zero]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

