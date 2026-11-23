module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0015
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonB
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0011
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronSer

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem desc_const (D : PowerSeries K) : constantCoeff (desc l D) = constantCoeff D := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    desc, PowerSeries.coeff_mk, mul_zero]

theorem desc_integral {D : PowerSeries K} (hD : IntegralPS D) : IntegralPS (desc l D) := by
  unfold IntegralPS at hD ⊢
  intro n
  rw [desc, PowerSeries.coeff_mk]
  exact hD _

theorem coeff_one_desc (D : PowerSeries K) : coeff 1 (desc l D) = coeff l D := by
  rw [desc, PowerSeries.coeff_mk, mul_one]

private theorem coeff_subst_X_pow_lemma (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]

theorem desc_congr (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (D : PowerSeries K)
    (hD : DivBy (l : K) (PowerSeries.derivative D)) :
    DivBy (l : K) (D - (desc l D).subst ((X : PowerSeries K) ^ l)) ∧
      IntegralPS (PowerSeries.derivative (desc l D)) := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hD' : ∀ n, ‖coeff n (PowerSeries.derivative D)‖ ≤ ‖(l : K)‖ := hD
  have hD2 : ∀ m, ‖coeff (m + 1) D‖ * ‖((m : K) + 1)‖ ≤ ‖(l : K)‖ := by
    intro m
    have h := hD' m
    rwa [PowerSeries.coeff_derivative, norm_mul] at h
  refine ⟨?_, ?_⟩
  · intro m
    rw [map_sub, coeff_subst_X_pow_lemma _ hl.ne_zero]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [desc, PowerSeries.coeff_mk, Nat.mul_div_cancel_left q hl.pos, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [sub_zero]
      have hm0 : m ≠ 0 := fun h => hd (h ▸ dvd_zero l)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h1 := hD2 m'
      have hu : ‖((m' : K) + 1)‖ = 1 := by
        have h2 := norm_natCast_of_coprime hl hl1 (m' + 1) hd
        push_cast at h2
        exact h2
      rwa [hu, mul_one] at h1
  · intro m
    rw [PowerSeries.coeff_derivative, desc, PowerSeries.coeff_mk, norm_mul]
    have e : l * (m + 1) - 1 + 1 = l * (m + 1) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hl.ne_zero (Nat.succ_ne_zero m)))
    have e2 : ((l * (m + 1) - 1 : ℕ) : K) + 1 = (l : K) * ((m : K) + 1) := by
      rw [← Nat.cast_add_one, e]
      push_cast
      ring
    have h1 := hD2 (l * (m + 1) - 1)
    rw [e2, e, norm_mul] at h1
    have h2 : ‖(l : K)‖ * (‖coeff (l * (m + 1)) D‖ * ‖((m : K) + 1)‖) ≤ ‖(l : K)‖ * 1 := by
      linarith [h1]
    exact le_of_mul_le_mul_left h2 hlpos

theorem desc_key {ι : Type} (hF : FrobField K l σ) {D : PowerSeries K}
    (hD0 : constantCoeff D = 0) (hD' : DivBy (l : K) (PowerSeries.derivative D)) (P : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero
      ((desc l D).subst (MvPowerSeries.map σ P)) - D.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  obtain ⟨h1, h2⟩ := desc_congr hF.prime hF.norm_l D hD'
  have hσP0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero hσP0)]
  have hfc := FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have hE0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand, hσP0]
  have hEi : IntegralMv (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) := by
    rw [integralMv_iff_divBy_one, divByMv_expand_iff, ← integralMv_iff_divBy_one]
    exact hF.integralMv_map hP
  have hPl0 : MvPowerSeries.constantCoeff (P ^ l) = 0 := by
    rw [map_pow, hP0, zero_pow hl0]
  have h3 := qls hF.prime hF.norm_l (desc l D) (by rw [desc_const, hD0]) h2
    (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) (P ^ l) hE0 hPl0 hEi
    (integralMv_pow hP l) (by
      have := divByMv_neg hfc
      rwa [neg_sub] at this)
  have h4 : (desc l D).subst (P ^ l) =
      PowerSeries.subst P ((desc l D).subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have h5 := divByMv_subst h1 hP0 hP
  rw [PowerSeries.subst_sub hPs, ← h4] at h5
  have := divByMv_sub h3 h5
  rwa [sub_sub_sub_cancel_right] at this

theorem desc_QCls (hF : FrobField K l σ) {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {b : K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : IntegralMv Φ) (hA0 : constantCoeff A = 0)
    (hA : IntegralPS A) (hb : ‖b‖ ≤ 1) {D : PowerSeries K} (hD : QCls l Φ A b D)
    (hD' : DivBy (l : K) (PowerSeries.derivative D)) :
    QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) b (desc l D) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  refine ⟨by rw [desc_const, hD.D0], (desc_congr hF.prime hF.norm_l D hD').2, ?_, ?_⟩
  · rw [← divByMv_expand_iff _ l hl0, map_sub, map_sub]
    have h1 := desc_key hF hD.D0 hD' Φ hΦ0 hΦ
    have h2 := desc_key hF hD.D0 hD' (MvPowerSeries.X (0 : Fin 2)) (by simp) (integralMv_X _)
    have h3 := desc_key hF hD.D0 hD' (MvPowerSeries.X (1 : Fin 2)) (by simp) (integralMv_X _)
    rw [MvPowerSeries.map_X] at h2 h3
    have h4 := divByMv_add (divByMv_sub (divByMv_sub h1 h2) h3) hD.add
    convert h4 using 1
    simp only [atX, atY]
    ring
  · rw [divBy_iff_mv, ← divByMv_expand_iff _ l hl0, map_sub, map_mul]
    have h1 := desc_key hF hD.D0 hD' (ι := Unit) A hA0 ((integralPS_iff_mv A).1 hA)
    have h2 := desc_key hF hD.D0 hD' (ι := Unit) (X : PowerSeries K) (by simp [PowerSeries.X])
      ((integralPS_iff_mv _).1 integralPS_X)
    rw [show MvPowerSeries.map σ (X : PowerSeries K) = (X : PowerSeries K) from PowerSeries.map_X σ,
      PowerSeries.X_subst, PowerSeries.X_subst] at h2
    have h3 := divByMv_mul_left ((integralPS_iff_mv _).1 (integralPS_C hb)) h2
    have h4 := divByMv_add (divByMv_sub h1 h3) ((divBy_iff_mv _ _).1 hD.eig)
    have hC : MvPowerSeries.expand l hl0 (C b : PowerSeries K) = (C b : PowerSeries K) :=
      PowerSeries.expand_C l hl0 b
    rw [hC]
    convert h4 using 1
    simp only [PowerSeries.map]
    ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
section
noncomputable section
open Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem norm_le_one_of_root {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have hsum := hm.as_sum
  rw [hsum] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := hlt.le
  have hn0 : P.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom ℂ_[l]) (P.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (P.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hc : ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ ≤ 1 := by
      rw [eq_intCast (Int.castRingHom ℂ_[l])]
      exact IsUltrametricDist.norm_intCast_le_one _ _
    calc ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (P.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (P.natDegree - 1) := one_mul _
  have heq := eq_neg_of_add_eq_zero_left h
  have h1 : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (P.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

theorem jInt : JInt := by
  intro d L hsf hd hL l _ ι
  obtain ⟨P, hm, hP⟩ := cm1 d L hsf hd hL
  refine norm_le_one_of_root P hm ?_
  have h := congrArg (ι : ℂ →+* ℂ_[l]) hP
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronPt
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def kronFun (p : ℕ) (τ : ℍ) : ℂ := Gm p τ + (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2

theorem kronSq_isMF (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)

theorem Gm_isMF' {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := (gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)

theorem kronFun_isMF {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (kronFun p) := (Gm_isMF' hp).add (kronSq_isMF p)

theorem aC_conv : Conv aC := convergesOnDisk_eisensteinFourCubeSeries
theorem dC_conv : Conv dC := convergesOnDisk_discriminantSeries
theorem aC_ev (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  exact evalSeries_eisensteinFourCubeSeries τ
theorem dC_ev (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  exact evalSeries_discriminantSeries τ

theorem kronFun_qExp {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl

theorem kronFun_div {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ qExpansion 1 (kronFun p) = PowerSeries.C (1 - zetaC p) * w := by
  obtain ⟨w, hw, hk⟩ := kronSer hp
  have hp0 : 0 < p := hp.pos
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩
  rw [kronFun_qExp hp]
  ext n
  have key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) =
      PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    simp [xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]
  have hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) =
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    rw [← gmQ_xp hp0]
    ext m
    simp only [xp, PowerSeries.coeff_mk, map_add (f := _)]
    split_ifs <;> simp
  rw [← key, hsum, hk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

theorem kronFun_poly {p : ℕ} (hp : p.Prime) :
    ∃ Q : Polynomial ℂ, (∀ i, Q.coeff i ∈ Rm p) ∧
      ∀ τ, kronFun p τ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * Q.eval (jT τ)) := by
  obtain ⟨w, hw, hqe⟩ := kronFun_div hp
  have hc0 : (1 - zetaC p) ≠ 0 := one_sub_zeta_ne_zero hp
  have hK := kronFun_isMF hp
  let f : ℍ → ℂ := fun τ => (1 - zetaC p)⁻¹ * kronFun p τ
  have hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f := hK.const_mul (1 - zetaC p)⁻¹
  have hwq : qExpansion 1 f = w := by
    apply hf.qExp_eq
    · have e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p) := by
        rw [hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [e]
      exact hK.conv.C_mul _
    · intro τ
      have hs := (hK.hasSum τ).mul_left (1 - zetaC p)⁻¹
      have hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n =
          (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n) := by
        intro n
        rw [hqe, PowerSeries.coeff_C_mul]
        field_simp
      unfold ev
      simp_rw [hw']
      exact hs.tsum_eq
  obtain ⟨P, hPc, -, hPe⟩ := qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)
  refine ⟨P, hPc, fun τ => ?_⟩
  calc kronFun p τ = (1 - zetaC p) * f τ := by
        rw [show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]

theorem kronPt {p : ℕ} (hp : p.Prime) {τ : ℍ} (h : Gm p τ = 0) :
    ∃ r : ℂ, IsIntegral ℤ r ∧ (jT τ ^ p - jT τ) ^ 2 = (1 - zetaC p) * r := by
  obtain ⟨Q, hQ, hK⟩ := kronFun_poly hp
  have hD := DD_ne_zero τ
  have hsq : ¬ IsSquare p := Irreducible.not_isSquare hp
  have hj := jT_isIntegral hp.pos hsq h
  have hint : IsIntegral ℤ (Q.eval (jT τ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)
  refine ⟨Q.eval (jT τ), hint, ?_⟩
  have e1 := hK τ
  unfold kronFun at e1
  rw [h, zero_add] at e1
  have hA : AA τ = jT τ * DD τ := by rw [jT, div_mul_cancel₀ _ hD]
  rw [hA] at e1
  have e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) =
      (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1)) := by
    linear_combination e1
  exact mul_right_cancel₀ (pow_ne_zero _ hD) e2

end ReciprocityTheory.ChartRestriction.L1
end
end

