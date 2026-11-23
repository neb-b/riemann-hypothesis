module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0018
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0013

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveFirstVariable
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser IsLawOfLog cob at1 in3 d1 swap2 DivAB BetaHyp)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable (p : ℕ) [hp : Fact p.Prime]

theorem sx_X_dvd_lX {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) ∣ sx_lX p i := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (sx_logF_const p)
  refine ⟨PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) g, ?_⟩
  unfold sx_lX
  rw [hg, PowerSeries.subst_mul hs, PowerSeries.subst_X hs]

theorem sx_divAB {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) : DivAB (inParam p be) := by
  intro n hn
  have hdvd : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ inParam p be := by
    intro i
    have hb : (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ be := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      by_contra hne
      have := h.ab m hne
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at hm
        omega
      · simp only [Fin.mk_one, Fin.isValue] at hm
        omega
    obtain ⟨g, hg⟩ := hb
    rw [hg, sx_inParam_mul, sx_inParam_X]
    exact Dvd.dvd.mul_right (sx_X_dvd_lX p i) _
  rcases hn with h0 | h1
  · exact MvPowerSeries.X_dvd_iff.1 (hdvd 0) n h0
  · exact MvPowerSeries.X_dvd_iff.1 (hdvd 1) n h1

variable {p}

theorem sx_two {τ : Type} {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem sx_log_law {F : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) {τ : Type} (u v : MvPowerSeries τ (K0 p))
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![u, v] F) (logF p) =
      PowerSeries.subst u (logF p) + PowerSeries.subst v (logF p) := by
  have hs : MvPowerSeries.HasSubst ![u, v] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩)
  have hc : PowerSeries.subst F (lgF (K0 p) p) = at1 0 (lgF (K0 p) p) + at1 1 (lgF (K0 p) p) := by
    have h0 := hF.2.2
    unfold cob at h0
    linear_combination h0
  have e := congrArg (MvPowerSeries.subst ![u, v]) hc
  rw [sx_subst_ps p hs hF.1, MvPowerSeries.subst_add hs, at1, at1,
    sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 0), sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs] at e
  rw [sx_logF_eq]
  simpa using e

theorem sx_law_const {F : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) {τ : Type} (u v : MvPowerSeries τ (K0 p))
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![u, v] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩))
    (Fin.forall_fin_two.2 ⟨hu, hv⟩) hF.1

theorem param_substitution_pair {τ : Type} [Finite τ] (be : MvPowerSeries (Fin 2) (K0 p)) (x y x' y' : MvPowerSeries τ (K0 p))
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (hx' : MvPowerSeries.constantCoeff x' = 0) (hy' : MvPowerSeries.constantCoeff y' = 0)
    (ex : PowerSeries.subst x' (logF p) = inParam p x) (ey : PowerSeries.subst y' (logF p) = inParam p y) :
    inParam p (sub2 p be x y) = MvPowerSeries.subst ![x', y'] (inParam p be) := by
  show inParam p (MvPowerSeries.subst ![x, y] be) = _
  apply sx_inParam_subst
  · intro i
    fin_cases i
    · simpa using hx
    · simpa using hy
  · intro i
    fin_cases i
    · simpa using hx'
    · simpa using hy'
  · intro i
    fin_cases i
    · simpa using ex
    · simpa using ey

theorem sx_eX {τ : Type} [Finite τ] (i : τ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ (K0 p)) (logF p) = inParam p (MvPowerSeries.X i) := by
  rw [sx_inParam_X]
  rfl

theorem sx_cX {τ : Type} (i : τ) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries τ (K0 p)) = 0 :=
  MvPowerSeries.constantCoeff_X i

theorem biadditive_first_variable {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    Formalism.InvariantFactorPaths.G7.Simeq (d1 F (inParam p be)) 0 := by
  have hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) (K0 p)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hin3 : MvPowerSeries.constantCoeff (in3 F) = 0 := sx_law_const hF _ _ (hX 0) (hX 1)
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) = 0 := by
    rw [map_add (f := _), hX 0, hX 1, add_zero]
  have ex : PowerSeries.subst (in3 F) (logF p) =
      inParam p (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) := by
    rw [in3, sx_log_law hF _ _ (hX 0) (hX 1), sx_inParam_add, ← sx_eX, ← sx_eX]
  have e1 := param_substitution_pair be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) (in3 F) (MvPowerSeries.X 2)
    h01 (hX 2) hin3 (hX 2) ex (sx_eX 2)
  have e2 := param_substitution_pair be (MvPowerSeries.X 0) (MvPowerSeries.X 2) (MvPowerSeries.X 0) (MvPowerSeries.X 2)
    (hX 0) (hX 2) (hX 0) (hX 2) (sx_eX 0) (sx_eX 2)
  have e3 := param_substitution_pair be (MvPowerSeries.X 1) (MvPowerSeries.X 2) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    (hX 1) (hX 2) (hX 1) (hX 2) (sx_eX 1) (sx_eX 2)
  have key : d1 F (inParam p be) = inParam p
      (sub2 p be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
        sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2) -
        sub2 p be (MvPowerSeries.X 1) (MvPowerSeries.X 2)) := by
    rw [th_inParam_sub, th_inParam_sub, e1, e2, e3]
    rfl
  rw [key]
  first
    | exact equiv_zero_of_integralExp p (integralExp_param_of_equiv_zero p h.add1)
    | exact equiv_zero_of_integralExp (integralExp_param_of_equiv_zero p h.add1)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExistsAtPiG1EqCPowMulIntegralSeries
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser' AA leadT G1)

section Scale

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem th_vp_ne (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) : vp ≠ 0 := by
  intro hv
  have hpos : p ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hp.out.one_lt)
  rw [hv, zero_pow hpos] at hvp
  have hp0 : (p : K') ≠ 0 := by
    rw [← map_natCast (algebraMap (K0 p) K')]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact hp0 hvp.symm

theorem th_wt_AA (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) {x y : Fin 2} (hxy : x ≠ y) (d : Fin 2 →₀ ℕ) :
    ∃ r ∈ Rp p K' vp, vp ^ d.degree * MvPowerSeries.coeff d (AA K' p x y - leadT K' p x y) = vp ^ (p + 1) * r := by
  classical
  have hp2 := hp.out.two_le
  rw [map_sub, Formalism.InvariantFactorPaths.G7.leadT_eq, MvPowerSeries.coeff_monomial]
  by_cases hd : d = Finsupp.single x 1 + Finsupp.single y p
  · have hx : d x = (p ^ 2) ^ 0 := by rw [hd]; simp [hxy.symm]
    have hy : d y = p * (p ^ 2) ^ 0 := by rw [hd]; simp [hxy]
    rw [if_pos hd, Formalism.InvariantFactorPaths.G7.coeff_AA_of K' hp2 le_rfl hx hy]
    exact ⟨0, (Rp p K' vp).zero_mem, by simp⟩
  · rw [if_neg hd, sub_zero]
    by_cases h : MvPowerSeries.coeff d (AA K' p x y) = 0
    · exact ⟨0, (Rp p K' vp).zero_mem, by rw [h]; simp⟩
    · obtain ⟨i, j, hij, hx, hy⟩ := Formalism.InvariantFactorPaths.G7.coeff_AA_ne_zero h
      have hj : 1 ≤ j := by
        by_contra hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        apply hd
        ext z
        rcases Formalism.InvariantFactorPaths.G7.finset_fin_two_eq_cases x y hxy z with rfl | rfl
        · simp [hx, hxy.symm]
        · simp [hy, hxy]
      have h4 : 4 ≤ p ^ 2 := by nlinarith
      obtain ⟨gi, hgi, hi', _⟩ := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred h4 i
      obtain ⟨gj, hgj, hj', _⟩ := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred h4 j
      have hle : i + j + 1 ≤ gi + p * gj := by nlinarith
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have hdeg : d.degree = (p ^ 2 - 1) * k + (p ^ 2 - 1) * (i + j + 1) + (p + 1) := by
        rw [Formalism.InvariantFactorPaths.G7.degree_fin_two_eq_add_of_ne hxy, hx, hy, hgi, hgj]
        have : (p ^ 2 - 1) * gi + 1 + p * ((p ^ 2 - 1) * gj + 1) = (p ^ 2 - 1) * (gi + p * gj) + (p + 1) := by ring
        rw [this, hk]
        ring
      refine ⟨(p : K') ^ k, (Rp p K' vp).pow_mem (natCast_mem _ p) k, ?_⟩
      rw [Formalism.InvariantFactorPaths.G7.coeff_AA_of K' hp2 hij hx hy, hdeg, pow_add, pow_add, pow_mul, pow_mul, hvp]
      have hp0 := pK'_ne p K'
      field_simp

theorem exists_atPi_G1_eq_C_pow_mul_integral_series (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) {c c' : K'} (hc : c ∈ Rp p K' vp)
    (hc' : c' ∈ Rp p K' vp) :
    ∃ Rr : MvPowerSeries (Fin 2) K', IntR (Rp p K' vp) Rr ∧ MvPowerSeries.constantCoeff Rr = 0 ∧
      atPi vp (G1 p c c') = MvPowerSeries.C (vp ^ (p + 1)) * Rr := by
  have hv : vp ^ (p + 1) ≠ 0 := pow_ne_zero _ (th_vp_ne p K' vp hvp)
  refine ⟨MvPowerSeries.C ((vp ^ (p + 1))⁻¹) * atPi vp (G1 p c c'), fun d => ?_, ?_, ?_⟩
  · obtain ⟨r1, hr1, e1⟩ := th_wt_AA p K' vp hvp (show (0 : Fin 2) ≠ 1 by decide) d
    obtain ⟨r2, hr2, e2⟩ := th_wt_AA p K' vp hvp (show (1 : Fin 2) ≠ 0 by decide) d
    rw [MvPowerSeries.coeff_C_mul]
    have e : MvPowerSeries.coeff d (atPi vp (G1 p c c')) = vp ^ (p + 1) * (c * r1 - c' * r2) := by
      show vp ^ d.degree * MvPowerSeries.coeff d (G1 p c c') = _
      unfold G1
      rw [map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
      linear_combination c * e1 - c' * e2
    rw [e, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]
    exact (Rp p K' vp).sub_mem ((Rp p K' vp).mul_mem hc hr1) ((Rp p K' vp).mul_mem hc' hr2)
  · rw [map_mul]
    have : MvPowerSeries.constantCoeff (atPi vp (G1 p c c')) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show vp ^ (0 : Fin 2 →₀ ℕ).degree * MvPowerSeries.coeff 0 (G1 p c c') = 0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.InvariantFactorPaths.G7.constant_coeff_g_one hp.out.ne_zero, mul_zero]
    rw [this, mul_zero]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hv, map_one, one_mul]

end Scale

theorem th_subst_scale {κ τ R : Type} [Finite κ] [CommRing R] (vp : R) (s : κ → MvPowerSeries τ R)
    (hs : MvPowerSeries.HasSubst s) (f : MvPowerSeries κ R) :
    MvPowerSeries.subst (fun k => MvPowerSeries.C vp * s k) f = MvPowerSeries.subst s (atPi vp f) := by
  rw [atPi_eq_rescale, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.smul_X _) hs]
  congr 1
  funext k
  have : ((fun _ : κ => vp) • (MvPowerSeries.X : κ → MvPowerSeries κ R)) k =
      MvPowerSeries.C vp * MvPowerSeries.X k := by
    rw [Pi.smul_apply', MvPowerSeries.smul_eq_C_mul]
  rw [this, ← MvPowerSeries.coe_substAlgHom hs, map_mul, MvPowerSeries.substAlgHom_X]
  congr 1
  exact ((MvPowerSeries.substAlgHom hs).commutes vp).symm

theorem th_map_Gser {p : ℕ} {K K2 : Type} [Field K] [Field K2] (φ : K →+* K2) (c c' : K) :
    MvPowerSeries.map φ (Gser p c c') = Gser p (φ c) (φ c') := by
  unfold Gser
  rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C]
  unfold Aser Aser'
  congr 2
  · funext n
    change φ (∑ i ∈ Finset.range (n 0 + 1), ∑ j ∈ Finset.range (n 1 + 1),
      if i ≤ j ∧ n 0 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, apply_ite, map_inv₀]
  · funext n
    change φ (∑ i ∈ Finset.range (n 1 + 1), ∑ j ∈ Finset.range (n 0 + 1),
      if i ≤ j ∧ n 1 = (p ^ 2) ^ i ∧ n 0 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, apply_ite, map_inv₀]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NumericalFamilyOfThreshold
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def nc_Need3 (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_Size D L Y u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem numerical_closed_of_threshold (C₀ : ℝ) (h9 : 9 ≤ C₀) (h : nc_Need3 C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_need C₀ fun D L X Y K h1 h2 h3 hr hs hT hL u w hg hlog t0 ht0 j hj =>
    have H := h D L X Y K h1 h2 h3 hr hs hT hL u w hg hlog t0 ht0 j hj
    ⟨nc_de X Y K hT hL u w hg t0 ht0 j hj (h9.trans h1) (h9.trans h2) hlog H.1, H.2⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem en_PhAt_const (hbe : BeProp p Y.be) (j : ℕ) (v : X.Pl) : MvPowerSeries.constantCoeff (Y.PhAt j v) = 0 := by
  unfold Pend.PhAt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)

theorem kernel_product_form (D : Formalism.BasicNotions.D7) : KernelProductForm X Y D := by
  intro hA j hj La La' h1 h2 φ
  obtain ⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  have hcz := charZero_K' p (K0 p)
  have hΨ : (∑ e : X.EA j, sub2 p Y.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
      MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, Y.PhAt j v := by
    unfold Pend.PhAt
    exact Fintype.sum_sigma _
  rw [hΨ] at hPh
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hE0 : E0 p (inParam p (Ph - ∑ v, Y.PhAt j v)) := ⟨th_inParam_const p hc0, h, hh0, hE⟩
  obtain ⟨w, hw⟩ := exp_neg_integral p hE0
  refine ⟨MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-(Ph - ∑ v, Y.PhAt j v))) * U0, ?_, ?_⟩
  · rw [en_inParamK_mul]
    refine en_IntR_mul ?_ hU0
    have e1 : inParam p (expS p (-(Ph - ∑ v, Y.PhAt j v))) = expK (inParam p (-(Ph - ∑ v, Y.PhAt j v))) := by
      unfold inParam
      exact th_subst_expK _ (fun i => by
        have := th_lX_const p (K0 p) i
        rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])
    rw [th_inParamK_map p (K0 p) Y.Kc, ← th_inParam_eq, e1, th_inParam_neg, hw]
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact Y.witt_mem_integers_Cp _
  · have e2 : -Ph = ∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v) := by
      rw [Finset.sum_neg_distrib]; ring
    have e3 : expS p (-Ph) = (∏ v, expS p (-Y.PhAt j v)) * expS p (-(Ph - ∑ v, Y.PhAt j v)) := by
      have a1 : expK (∑ v, (-Y.PhAt j v) + -(Ph - ∑ v, Y.PhAt j v)) =
          expK (∑ v, (-Y.PhAt j v)) * expK (-(Ph - ∑ v, Y.PhAt j v)) :=
        expK_add (by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          exact Finset.sum_eq_zero fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero])
          (by rw [map_neg, hc0, neg_zero])
      have a2 : expK (∑ v, (-Y.PhAt j v)) = ∏ v, expK (-Y.PhAt j v) :=
        th_expK_sum _ _ fun v _ => by rw [map_neg, en_PhAt_const X Y hbe, neg_zero]
      rw [e2]
      exact a1.trans (by rw [a2]; rfl)
    rw [hTh, e3, map_mul, map_prod, mul_assoc]
    rfl

theorem restPlaces (D : Formalism.BasicNotions.D7) : RestPlaces X Y D := restPlaces_of D (kernel_product_form X Y D)

theorem restEnt_of (D : Formalism.BasicNotions.D7) (h2 : PlacewiseLowerBoundEvenShift X Y D) (hB : RestBU X Y D) (hA : admitted D X Y) : EntCondition X Y :=
  restEnt_of_rest D (restPlaces X Y D) h2 hB hA

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

