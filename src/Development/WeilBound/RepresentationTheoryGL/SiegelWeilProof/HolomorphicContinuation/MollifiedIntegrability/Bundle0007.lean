module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.EvXPderivPhiP
section
noncomputable section

open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem amat_det_ne (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) : (Amat ε c t b a).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hA : Amat ε c t b a *ᵥ v = (c : ℂ) • v - (Complex.I * t * sgn ε a) • (bᵀ *ᵥ v) := by
    rw [Amat, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec]
  have key : (c : ℂ) * (star v ⬝ᵥ v) - (Complex.I * t * sgn ε a) * (star v ⬝ᵥ (bᵀ *ᵥ v)) = 0 := by
    have h1 : star v ⬝ᵥ (Amat ε c t b a *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
    rw [hA, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have hq : (star v ⬝ᵥ (bᵀ *ᵥ v)).im = 0 := hb.transpose.im_star_dotProduct_mulVec_self v
  have hd : (star v ⬝ᵥ v).im = 0 := by
    have := Matrix.isHermitian_one.im_star_dotProduct_mulVec_self (𝕜 := ℂ) v
    rwa [one_mulVec] at this
  have hq' : star v ⬝ᵥ (bᵀ *ᵥ v) = ((star v ⬝ᵥ (bᵀ *ᵥ v)).re : ℂ) := Complex.ext (by simp) (by simp [hq])
  have hs' : sgn ε a = ((if ε a then 1 else -1 : ℝ) : ℂ) := by unfold sgn; split_ifs <;> simp
  have h0re : (Complex.I * t * sgn ε a * (star v ⬝ᵥ (bᵀ *ᵥ v))).re = 0 := by
    rw [hq', hs']; simp [Complex.mul_re]
  have hre := congrArg Complex.re key
  rw [Complex.sub_re, h0re, Complex.re_ofReal_mul, Complex.zero_re, sub_zero] at hre
  have hdre : (star v ⬝ᵥ v).re = 0 := by
    rcases mul_eq_zero.mp hre with h | h
    · exact absurd h hc.ne'
    · exact h
  have hd0 : star v ⬝ᵥ v = 0 := Complex.ext hdre hd
  exact hv0 (dotProduct_star_self_eq_zero.mp hd0)

theorem dEv_apply (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    dEv P x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
  simp [dEv, evX_eq, mul_comm]

theorem evX_continuous (P : PX m n) : Continuous (evX P) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

theorem crd_wirt (a : Fin m) (j : Fin n) (k : Fin m × Fin n × Bool) :
    crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      if k = (a, j, false) then 2 else 0 := by
  obtain ⟨a', i', bb⟩ := k
  rw [crd_apply, crd_apply]
  by_cases h : a' = a ∧ i' = j
  · obtain ⟨rfl, rfl⟩ := h
    cases bb <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · have h' : ¬ ((a', i', bb) = (a, j, false)) := by intro e; simp at e; exact h ⟨e.1, e.2.1⟩
    simp [h, h']

theorem dEv_wirt (P : PX m n) (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    dEv P x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * dEv P x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      2 * evX (pderiv (a, j, false) P) x := by
  simp only [dEv, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (a, j, false)]
  · have := crd_wirt a j (a, j, false); simp only [if_true] at this
    rw [← this]; ring
  · intro k _ hk
    have := crd_wirt a j k; rw [if_neg hk] at this
    calc _ = evX (pderiv k P) x * (crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0)) := by ring
      _ = 0 := by rw [this, mul_zero]
  · simp

theorem evX_pderiv_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ)
    (a : Fin m) (j : Fin n) :
    evX (pderiv (a, j, false) (phiP ε c t b)) x = -∑ k, (Amat ε c t b a) k j * star (x a k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [phiP, map_neg, map_sum, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [evX, map_neg, map_sum, map_mul, Prod.ext_iff]
  simp only [mul_zero, mul_one, zero_mul, Pi.single_apply, Prod.mk.injEq, and_true, Bool.false_eq_true, and_false,
    if_false, map_zero, add_zero, zero_add]
  rw [neg_inj, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro a' _ ha; simp [ha]
  · simp

end PositivityTheory.Rg.Sw.WR.G
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ExpCombine
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem exp_combine (t : ℝ) (y q β : E n) :
    Complex.exp (Complex.I * t * ip y q) * Complex.exp (-(Complex.I * t * ip β y)) =
      Complex.exp (Complex.I * t * ip y (q - β)) := by
  rw [ip_sub_right, ip_comm β y, ← Complex.exp_add]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1000000 in
theorem step_a (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (β : E n) :
    ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
        Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * kr ε t (qq x - β) ∂μ := by
  have hfun : ∀ (y : E n) (x : X), Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) := by
    intro y x
    rw [← exp_combine]
    ring
  have hL : ∀ y : E n, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) ∂μ := by
    intro y
    rw [← integral_mul_const, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => hfun y x)
  have hm1 : Measurable fun p : E n × X => ip p.1 (qq p.2 - β) :=
    continuous_ip.measurable.comp (measurable_fst.prodMk ((hqq.comp measurable_snd).sub_const β))
  have hm2 : Measurable fun p : E n × X => Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β)) :=
    ((Complex.measurable_ofReal.comp hm1).const_mul (Complex.I * t)).cexp
  have hint : Integrable (fun p : E n × X =>
      Ψ p.2 * (gam ε p.1 * Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono ((integrable_gauss (n := n) ε hε).mul_prod hΨ) ?_ ?_
    · exact (hΨ.1.comp_snd (μ := (volume : Measure (E n)))).mul
        ((((continuous_gam ε).measurable.comp measurable_fst).mul hm2).aestronglyMeasurable)
    · refine Eventually.of_forall fun p => ?_
      simp only [norm_mul, norm_cexp_It, mul_one]
      exact le_of_eq (mul_comm _ _)
  simp only [hL, kr, ← integral_const_mul]
  exact integral_integral_swap hint

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.RatBound
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ratBound (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 p q R)) y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
  obtain ⟨hUo, hFc, c₀, C₀, hc₀, hb⟩ := hB n s hs p q R
  set K : ℝ := ((N * n : ℕ) : ℝ) with hK
  set C₁ : ℝ := max C₀ 0 with hC₁
  refine ⟨(Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁, fun y => ?_⟩
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  set w : Fin n → ℝ := fun i => 1 + |lam i| with hw
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw]; positivity
  set W : ℝ := ∏ i, w i with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => hwpos i
  set d : Mc n := Matrix.diagonal (fun i => (lam i : ℂ)) with hd
  set ρ : Fin n → Fin n → ℝ := fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|)) with hρ
  have hρpos : ∀ i j, 0 < ρ i j := fun i j => mul_pos hc₀ (Real.sqrt_pos.2 (mul_pos (hwpos i) (hwpos j)))
  have hlink := (hL n (Fr s p q R) (Ugood s) hUo hFc (herm_mem_Ugood s hs)).1 N y
  rw [cls_zero, hlink, hy]
  set F' : Mc n → ℂ := fun c => Fr s p q R (k * c * kᴴ) with hF'
  set U' : Set (Mc n) := {c | k * c * kᴴ ∈ Ugood s} with hU'
  have hU'o : IsOpen U' := hUo.preimage (contDiff_conj k).continuous
  have hF'c : ContDiffOn ℂ (⊤ : ℕ∞) F' U' := hFc.comp (contDiff_conj k).contDiffOn (fun c hc => hc)
  have hdisc : pdisc d ρ ⊆ U' := fun b hb' => (hb k hk lam b hb').1
  have hdmem : d ∈ U' := hdisc (fun i j => by simp [hρpos i j |>.le])
  have hherm' : ∀ y', herm y' ∈ U' := fun y' => conj_mem_Ugood s k hk _ (herm_mem_Ugood s hs y')
  rw [← hI n (Fr s p q R) (Ugood s) hUo hFc k hk N d hdmem, (hL n F' U' hU'o hF'c hherm').2 N d hdmem]
  have hM : ∀ b ∈ pdisc d ρ, ‖F' b‖ ≤ C₁ * W ^ (-((p + q : ℕ) : ℝ)) := fun b hb' =>
    ((hb k hk lam b hb').2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hWpos.le _))
  have hword : ∀ τ : Fin N → Equiv.Perm (Fin n),
      ‖word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖ ≤
        ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
    intro τ
    have h := hC n F' U' hU'o hF'c d ρ hρpos hdisc _ hM ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    rw [prod_blocks N (fun j k => (((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)).length : ℝ) /
      ρ (τ j k) k)]
    rw [length_blocks]
    show ∏ j, ∏ k, K / ρ ((τ j) k) k = ((K / c₀) ^ n / W) ^ N
    have hblock : ∀ j, ∏ k, K / ρ ((τ j) k) k = (K / c₀) ^ n / W := by
      intro j
      have hs := prod_sqrt_perm (τ j) w hwpos
      simp only [hw] at hs
      simp only [hρ]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs, div_pow]
      simp only [hW, hw]
      field_simp
    rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsgn : ∀ τ : Fin N → Equiv.Perm (Fin n), ‖(((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))‖ = 1 := by
    intro τ
    have h : ∀ j, |((Equiv.Perm.sign (τ j) : ℤ))| = 1 := fun j => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (τ j)) with h | h <;> simp [h]
    have h2 : |∏ j, ((Equiv.Perm.sign (τ j) : ℤ))| = 1 := by
      rw [Finset.abs_prod, Finset.prod_eq_one fun j _ => h j]
    rw [Complex.norm_intCast]
    exact_mod_cast h2
  have hdP : dP y ≤ W ^ (2 : ℝ) := by
    rw [dP_of_spectral y k hk lam hy, Real.rpow_two, hW, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    simp only [hw]
    have : lam i ^ 2 = |lam i| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (lam i)]
  have hWe : ∀ e : ℝ, 0 ≤ e → W ^ (-e) ≤ (dP y) ^ (-e / 2) := by
    intro e he
    have h1 : W ^ (-e) = (W ^ (2 : ℝ)) ^ (-e / 2) := by
      rw [← Real.rpow_mul hWpos.le]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow_of_nonpos (dP_pos y) hdP (by linarith)
  calc ‖∑ τ : Fin N → Equiv.Perm (Fin n), (((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ)) *
          word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖
      ≤ ∑ τ : Fin N → Equiv.Perm (Fin n), ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        rw [norm_mul, hsgn τ, one_mul]; exact hword τ
    _ = (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (W ^ (-((p + q + N : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : W ^ (-((p + q + N : ℕ) : ℝ)) = W ^ (-((p + q : ℕ) : ℝ)) * (W ^ N)⁻¹ := by
          rw [show (-((p + q + N : ℕ) : ℝ)) = (-((p + q : ℕ) : ℝ)) + (-(N : ℝ)) by push_cast; ring,
            Real.rpow_add hWpos, Real.rpow_neg hWpos.le, Real.rpow_natCast, Real.rpow_neg hWpos.le, Real.rpow_natCast]
        rw [this, div_pow]; ring
    _ ≤ (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left (hWe _ (by positivity)) ?_
        refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg (div_nonneg (by positivity) hc₀.le) _) _))
          (le_max_right _ _)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepB
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

set_option maxHeartbeats 1000000 in
theorem step_b (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (C : ℂ) :
    ∫ β, ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ)) =
      ∫ x, Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) ∂μ := by
  have hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1)) :=
    (continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)
  have hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ) :=
    hΨ.aestronglyMeasurable.comp_snd
  have hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ) :=
    (hψc.measurable.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖))
      (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨β, x⟩ := p
    show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)
    rw [norm_mul, norm_mul, norm_mul]
    have hk := norm_kr_le ε t hε (qq x - β)
    calc ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ‖kr ε t (qq x - β)‖)) ≤
          ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ∫ y, ‖gam (n := n) ε y‖)) := by gcongr
      _ = ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖) := by ring
  have e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) =
      fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ := by
    funext β
    rw [← integral_const_mul, ← integral_const_mul]
  have e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) =
      fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext β
    ring
  rw [e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepC
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

set_option maxHeartbeats 1000000 in
theorem step_c (ψ : E n → ℂ) (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε) (w : E n) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t (w - β)) =
      mM ψ (|t| / (2 * Real.sqrt ε)) w := by
  have hlpos : 0 < |t| / (2 * Real.sqrt ε) := div_pos (abs_pos.2 ht) (by have := Real.sqrt_pos.2 hε; positivity)
  set l := |t| / (2 * Real.sqrt ε) with hl
  have hk : ∀ u : E n, (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t u =
      (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := fun u => kraw_eq ε hε t ht u
  simp_rw [hk]
  have h1 : ∫ β, ψ β * (((l ^ (n ^ 2) * gK (l • (w - β))) : ℝ) : ℂ) =
      ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := by
    have := integral_sub_left_eq_self (μ := (volume : Measure (E n)))
      (fun u => ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)) w
    simpa only [sub_sub_cancel] using this
  rw [h1]
  have h2 := Measure.integral_comp_smul (μ := (volume : Measure (E n))) (fun v : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ)) l
  simp only [inv_smul_smul₀ hlpos.ne'] at h2
  rw [finrank_E] at h2
  unfold mM
  calc ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)
      = ((l ^ (n ^ 2) : ℝ) : ℂ) * ∫ u, ψ (w - u) * (gK (l • u) : ℂ) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        push_cast
        ring
    _ = ((l ^ (n ^ 2) : ℝ) : ℂ) * (|(l ^ (n ^ 2))⁻¹| • ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)) := by rw [h2]
    _ = ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ) := by
        rw [abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (pow_pos hlpos _).ne', Complex.ofReal_one, one_mul]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

