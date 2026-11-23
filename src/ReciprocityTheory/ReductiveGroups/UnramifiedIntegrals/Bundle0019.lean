module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0018

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonF
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem HD.map_frobenius_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map (σ.comp σ) lam) (MvPowerSeries.map (σ.comp σ) Φ)
      (PowerSeries.map (σ.comp σ) A) a := by
  have hτa : (σ.comp σ) a = a := h.a_sq
  have e := congrArg (PowerSeries.map (σ.comp σ)) h.Alog
  rw [map_mul, PowerSeries.map_C, hτa] at e
  have e2 := congrArg (MvPowerSeries.map (σ.comp σ)) h.log
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, h.a_ne, h.a_sq⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, map_zero]
  · rw [PowerSeries.coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact (integralMv_iff_divBy_one Φ).mp h.Φint d
  · have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    unfold atX atY at e2 ⊢
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0), map_add (f := _),
      PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), MvPowerSeries.map_X,
      MvPowerSeries.map_X] at e2
    exact e2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.A0, map_zero]
  · unfold IntegralPS
    intro n
    rw [PowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact h.Aint n
  · have e' : MvPowerSeries.map (σ.comp σ) (lam.subst A) = C a * PowerSeries.map (σ.comp σ) lam := e
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h.A0)] at e'
    exact e'

theorem HD.map_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by
  induction i with
  | zero =>
    simp only [pow_zero, RingHom.one_def, MvPowerSeries.map_id, PowerSeries.map_id, RingHom.id_apply]
    exact h
  | succ i ih =>
    have h1 := HD.map_frobenius_sq hF ih
    simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
      RingHom.comp_apply]
    exact h1

theorem honF_subst_subst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem honF_integral_subst {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS (f.subst g) :=
  (integralPS_iff_mv _).mpr (integralMv_subst hf hg0 ((integralPS_iff_mv g).mp hg))

theorem hon_mu (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by
  have hl := hF.prime
  have hl1 := hF.norm_l
  have hlam' : IntegralPS (PowerSeries.derivative lam) := h.toLawD.deriv_integral
  have h' := h.map_frobenius_sq hF
  have Hh : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh1.g0
  have HΦ' : PowerSeries.HasSubst (MvPowerSeries.map (σ.comp σ) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h'.Φ0
  have HA' : PowerSeries.HasSubst (PowerSeries.map (σ.comp σ) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h'.A0
  have HA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' h.A0
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hXq0 : constantCoeff ((X : PowerSeries K) ^ (l ^ 2)) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have HXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXq0
  have hX0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have HX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (hX0 i)
  have hp0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (![atX hh, atY hh] i) = 0 := by
    intro i
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 0) hh hh1.g0
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 1) hh hh1.g0
  have hpI : ∀ i : Fin 2, IntegralMv (![atX hh, atY hh] i) := by
    intro i
    fin_cases i
    · exact integralMv_subst hh1.gInt (hX0 0) (integralMv_X 0)
    · exact integralMv_subst hh1.gInt (hX0 1) (integralMv_X 1)
  have Hp : MvPowerSeries.HasSubst ![atX hh, atY hh] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hp0
  refine ⟨⟨PowerSeries.constantCoeff_subst_eq_zero hh1.g0 lam h.lam0, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [derivative_subst Hh]
    exact integralPS_mul (honF_integral_subst hlam' hh1.g0 hh1.gInt) (integralPS_derivative hh1.gInt)
  · have key := qls hl hl1 lam h.lam0 hlam' (hh.subst (MvPowerSeries.map (σ.comp σ) Φ))
      (Φ.subst ![atX hh, atY hh])
      (PowerSeries.constantCoeff_subst_eq_zero h'.Φ0 hh hh1.g0)
      (MvPowerSeries.constantCoeff_subst_eq_zero Hp hp0 h.Φ0)
      (integralMv_subst hh1.gInt h'.Φ0 h'.Φint) (integralMv_subst2 h.Φint hp0 hpI) hh1.add
    have ex : atX (lam.subst hh) = lam.subst (atX hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 0) lam
    have ey : atY (lam.subst hh) = lam.subst (atY hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 1) lam
    have ax : (atX lam).subst ![atX hh, atY hh] = lam.subst (atX hh) :=
      (honF_subst_subst lam (hX0 0) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have ay : (atY lam).subst ![atX hh, atY hh] = lam.subst (atY hh) :=
      (honF_subst_subst lam (hX0 1) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have e1 : lam.subst (Φ.subst ![atX hh, atY hh]) = atX (lam.subst hh) + atY (lam.subst hh) := by
      rw [ex, ey, ← honF_subst_subst lam h.Φ0 Hp, h.log, MvPowerSeries.subst_add Hp, ax, ay]
    rw [e1] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HΦ', sub_sub]
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' (hh.subst (PowerSeries.map (σ.comp σ) A))
      (A.subst hh) (PowerSeries.constantCoeff_subst_eq_zero h'.A0 hh hh1.g0)
      (PowerSeries.constantCoeff_subst_eq_zero hh1.g0 A h.A0)
      (honF_integral_subst hh1.gInt h'.A0 h'.Aint) (honF_integral_subst h.Aint hh1.g0 hh1.gInt) hh1.eig
    rw [← PowerSeries.subst_comp_subst_apply HA Hh, h.Alog, PowerSeries.subst_mul Hh,
      PowerSeries.subst_C] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HA']
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' e (hh.subst ((X : PowerSeries K) ^ (l ^ 2))) he0
      (PowerSeries.constantCoeff_subst_eq_zero hXq0 hh hh1.g0) he
      (honF_integral_subst hh1.gInt hXq0 (integralPS_pow integralPS_X _)) hh2
    rw [hlog] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HXq]
    exact key
  · rw [Formalism.LT.PadicP.coeff_one_subst lam hh h.lam0 hh1.g0, h.lam1, one_mul]

theorem lemmaQ_tw (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) {D : PowerSeries K}
    (hD : QCls l (MvPowerSeries.map ((σ.comp σ) ^ i) Φ) (PowerSeries.map ((σ.comp σ) ^ i) A) a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
        (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * PowerSeries.map ((σ.comp σ) ^ i) lam
        - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  obtain ⟨Dp, hDp, hdiv⟩ := lemmaQ hF (HD.map_sq hF h i) hD
  refine ⟨Dp, ?_, hdiv⟩
  simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
    RingHom.comp_apply]
  exact hDp

theorem hon_series (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : ℕ → K, ‖c 0‖ = 1 ∧ (∀ i, ‖c i‖ ≤ 1) ∧ ∀ N : ℕ, ∃ R : PowerSeries K,
      constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam).subst
              ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1)))) := by
  obtain ⟨hh, hhom, hdiv, hc1⟩ := hon_shape hF h he0 he hlog
  obtain ⟨hQ, hmod, hcoef⟩ := hon_mu hF h he0 he hlog hhom hdiv
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hQ' : QCls l (MvPowerSeries.map ((σ.comp σ) ^ (0 + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (0 + 1)) A) a (lam.subst hh) := by
    simpa using hQ

  let seq : (i : ℕ) → {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D} := fun i =>
    Nat.rec (motive := fun i => {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D}) ⟨lam.subst hh, hQ'⟩
      (fun i D => ⟨Classical.choose (lemmaQ_tw hF h (i + 1) D.2),
        (Classical.choose_spec (lemmaQ_tw hF h (i + 1) D.2)).1⟩) i
  have hstep : ∀ i, DivBy (l : K) ((seq i).1 - C (coeff 1 (seq i).1) *
      PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam - (seq (i + 1)).1.subst ((X : PowerSeries K) ^ (l ^ 2))) :=
    fun i => (Classical.choose_spec (lemmaQ_tw hF h (i + 1) (seq i).2)).2

  have hsub : ∀ m : ℕ, m ≠ 0 → PowerSeries.HasSubst ((X : PowerSeries K) ^ m) := fun m hm =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hm])
  have hcomp : ∀ (f : PowerSeries K) (m q : ℕ), m ≠ 0 → q ≠ 0 →
      PowerSeries.subst ((X : PowerSeries K) ^ m) (f.subst ((X : PowerSeries K) ^ q) : PowerSeries K) =
        f.subst ((X : PowerSeries K) ^ (m * q)) := by
    intro f m q hm hq
    rw [PowerSeries.subst_comp_subst_apply (hsub q hq) (hsub m hm)]
    congr 1
    rw [← PowerSeries.coe_substAlgHom (hsub m hm), map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (hsub m hm), ← pow_mul]
  refine ⟨fun i => coeff 1 (seq i).1, ?_, fun i => (seq i).2.norm_coeff_one,
    fun N => ⟨(seq N).1, (seq N).2.D0, ?_⟩⟩
  · show ‖coeff 1 (lam.subst hh)‖ = 1
    rw [hcoef, hc1]
    exact hon_level hF h he0 he hlog hlev
  · induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, pow_one]
      exact hmod
    | succ N ih =>
      have hm : (l ^ 2) ^ (N + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl0)
      have h1 := (divBy_expand_iff (l : K) ((l ^ 2) ^ (N + 1)) hm _).2 (hstep N)
      rw [← PowerSeries.coe_substAlgHom (hsub _ hm), map_sub, map_sub, ← PowerSeries.smul_eq_C_mul,
        map_smul, PowerSeries.smul_eq_C_mul, PowerSeries.coe_substAlgHom, hcomp _ _ _ hm (pow_ne_zero _ hl0), ← pow_succ] at h1
      have := divBy_add ih h1
      convert this using 1
      simp only [Finset.sum_range_succ]
      ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.G2EqZeroOfHasCMByThree
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_three_sq : omegaK 3 ^ 2 = omegaK 3 - 1 := by
  have h : (((Real.sqrt (3 : ℕ) : ℝ) : ℂ)) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  unfold omegaK
  linear_combination (Complex.I ^ 2 / 4) * h + (3 / 4 : ℂ) * Complex.I_sq

def mulOmegaEquiv (L : PeriodPair) (hCM : HasCMBy 3 L) : L.lattice ≃ L.lattice where
  toFun l := ⟨omegaK 3 * l, hCM l l.2⟩
  invFun l := ⟨(l : ℂ) - omegaK 3 * l, L.lattice.sub_mem l.2 (hCM l l.2)⟩
  left_inv l := by
    apply Subtype.ext
    show omegaK 3 * (l : ℂ) - omegaK 3 * (omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq
  right_inv l := by
    apply Subtype.ext
    show omegaK 3 * ((l : ℂ) - omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq

theorem g2_eq_zero_of_hasCMBy_three (L : PeriodPair) (hCM : HasCMBy 3 L) : L.g₂ = 0 := by
  have hsq := omegaK_three_sq
  have h4 : omegaK 3 ^ 4 = -omegaK 3 := by
    linear_combination (omegaK 3 ^ 2 + omegaK 3) * hsq
  have h0 : omegaK 3 ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have h1 : omegaK 3 ≠ -1 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have key : L.G 4 = (omegaK 3 ^ 4)⁻¹ * L.G 4 := by
    conv_lhs => rw [PeriodPair.G, ← (mulOmegaEquiv L hCM).tsum_eq]
    rw [PeriodPair.G, ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    show ((omegaK 3 * (l : ℂ)) ^ 4)⁻¹ = _
    rw [mul_pow, mul_inv]
  have hG : L.G 4 = 0 := by
    have h40 : omegaK 3 ^ 4 ≠ 0 := pow_ne_zero _ h0
    have h2 : omegaK 3 ^ 4 * L.G 4 = L.G 4 := by
      conv_lhs => rw [key]
      rw [mul_inv_cancel_left₀ h40]
    rw [h4] at h2
    have h3 : (omegaK 3 + 1) * L.G 4 = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (by linear_combination h) h1
    · exact h
  rw [PeriodPair.g₂, hG, mul_zero]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedGcd
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem rootPoly_monic' {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

theorem rootPoly_inter_mul_sdiff {E : Type} [Field E] (xs ys : Finset E) :
    rootPoly (xs ∩ ys) * rootPoly (xs \ ys) = rootPoly xs := by
  unfold rootPoly
  rw [← Finset.prod_union (Finset.disjoint_sdiff_inter xs ys).symm, Finset.union_comm,
    Finset.sdiff_union_inter]

theorem rootPoly_isCoprime_of_disjoint {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by
  unfold rootPoly
  refine IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  have hne : x ≠ y := fun e => Finset.disjoint_left.1 h hx (e ▸ hy)
  exact (sub_ne_zero.2 hne).isUnit

theorem exists_poly_map_subfield {E : Type} [Field E] [DecidableEq E] (k : Subfield E) (P : E[X])
    (h : ∀ i, P.coeff i ∈ k) : ∃ p : (k)[X], p.map k.subtype = P := by
  have : P ∈ Polynomial.lifts k.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  exact this

theorem rootPoly_inter_mem {E : Type} [Field E] (k : Subfield E) (xs ys : Finset E)
    (hx : ∀ i, (rootPoly xs).coeff i ∈ k) (hy : ∀ i, (rootPoly ys).coeff i ∈ k) :
    ∀ i, (rootPoly (xs ∩ ys)).coeff i ∈ k := by
  obtain ⟨p, hp⟩ := exists_poly_map_subfield k _ hx
  obtain ⟨q, hq⟩ := exists_poly_map_subfield k _ hy
  set R := rootPoly (xs ∩ ys) with hR
  set g0 := EuclideanDomain.gcd p q with hg0
  set g := g0.map k.subtype with hg
  have hgP : g ∣ rootPoly xs := by
    rw [← hp]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)
  have hgQ : g ∣ rootPoly ys := by
    rw [← hq]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)
  have hA := rootPoly_inter_mul_sdiff xs ys
  have hB := rootPoly_inter_mul_sdiff ys xs
  rw [Finset.inter_comm ys xs] at hB
  have hdisj : Disjoint (xs \ ys) (ys \ xs) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  obtain ⟨u, v, huv⟩ := rootPoly_isCoprime_of_disjoint _ _ hdisj
  have hgR : g ∣ R := by
    have : R = u * rootPoly xs + v * rootPoly ys := by
      rw [← hA, ← hB]
      linear_combination (-R) * huv
    rw [this]
    exact dvd_add (hgP.mul_left _) (hgQ.mul_left _)
  have hRg : R ∣ g := by
    have e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys) := by
      rw [← hp, ← hq, Polynomial.gcd_map]
    rw [e]
    exact EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩
  have hRm : R.Monic := rootPoly_monic' _
  have hg0' : g ≠ 0 := fun e => hRm.ne_zero (by simpa [e] using hgR)
  have hg00 : g0 ≠ 0 := fun e => hg0' (by rw [hg, e, Polynomial.map_zero])
  have hmon : (g0 * C g0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hg00
  have hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic := hmon.map _
  have hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R := by
    have h1 : Associated g R := associated_of_dvd_dvd hgR hRg
    refine Associated.trans ?_ h1
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (associated_mul_unit_left g _ ?_).symm.symm
    refine Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)
    simpa using hg00
  have heq := eq_of_monic_of_associated hmon' hRm hassoc
  intro i
  rw [← heq, Polynomial.coeff_map]
  exact (((g0 * C g0.leadingCoeff⁻¹).coeff i)).2

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProjA
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] (U : PowerSeries K)

theorem homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem homS_sub (m : ℕ) (P Q : K[X]) : homS U m (P - Q) = homS U m P - homS U m Q := by
  simp only [homS, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem homS_zero (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]

theorem homS_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]

theorem homS_monomial (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial_of_ne a hb]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring

theorem homS_eq_zero (hU : PowerSeries.constantCoeff U = 1) (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (h : homS U m P = 0) : P = 0 := by
  have h1 : PowerSeries.coeff (2 * (m - P.natDegree)) (homS U m P) = P.leadingCoeff := by
    unfold homS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single P.natDegree]
    · rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, map_pow, hU]
      simp
    · intro b hb hne
      have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp
    · intro hh
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hP)) hh
  rw [h, map_zero] at h1
  exact leadingCoeff_eq_zero.1 h1.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

