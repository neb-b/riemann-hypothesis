module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
section
noncomputable section

namespace Formalism.L2.Th1.E

namespace ScaledModelNorms

open Formalism.L2.Th1

theorem dwp_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (F.scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  have h := F.Homog.tsum_scale L c hc (fun w => -2 / (c * z - w) ^ 3)
  rw [← (PeriodPair.hasSum_derivWeierstrassP _ (c * z)).tsum_eq,
    ← (PeriodPair.hasSum_derivWeierstrassP L z).tsum_eq, h, ← tsum_mul_left]
  congr 1
  funext w
  rw [← mul_sub, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

variable (l : ℕ) [Fact l.Prime]

theorem norm_nat {N : ℕ} (h : ¬ l ∣ N) : ‖(N : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  have e : (N : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (N : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    simp
  rw [e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 h

theorem norm_two (hl : 5 ≤ l) : ‖(2 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  simpa using norm_nat l h

theorem norm_four (hl : 5 ≤ l) : ‖(4 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  simpa using norm_nat l h

theorem intCurve_short (hl : 5 ≤ l) (g2 g3 : ℂ_[l]) (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (hD : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) : IntCurve (A.shortW g2 g3) := by
  have hΔ : (A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
    simp only [A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [A.shortW]
  · simp [A.shortW]
  · simp [A.shortW]
  · show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, norm_four l hl, div_one]; exact h2
  · show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, norm_four l hl, div_one]; exact h3
  · rw [hΔ]; exact hD

variable (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem nonsing (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (PeriodPair.derivWeierstrassP_sq L t ht)
  simp only [map_sub, map_mul, map_pow, map_ofNat] at h
  show (ι (L.derivWeierstrassP t) / 2) ^ 2 + 0 * ι (L.weierstrassP t) * (ι (L.derivWeierstrassP t) / 2) +
      0 * (ι (L.derivWeierstrassP t) / 2) =
    ι (L.weierstrassP t) ^ 3 + 0 * ι (L.weierstrassP t) ^ 2 + (-ι L.g₂ / 4) * ι (L.weierstrassP t) +
      (-ι L.g₃ / 4)
  linear_combination (1 / 4 : ℂ_[l]) * h

theorem ptOf_notMem (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (nonsing l L ι hΔ t ht) := by
  unfold ptOf
  rw [dite_eq_left ⟨ht, nonsing l L ι hΔ t ht⟩]

theorem px_ptOf (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    px (curveL l L ι) (ptOf l L ι t) = ι (L.weierstrassP t) := by
  rw [ptOf_notMem l L ι hΔ t ht]
  rfl

theorem py_ptOf (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    py (curveL l L ι) (ptOf l L ι t) = ι (L.derivWeierstrassP t) / 2 := by
  rw [ptOf_notMem l L ι hΔ t ht]
  rfl

end ScaledModelNorms


open Formalism.L2.Th1 in
theorem cm_integrality_of_torsion_points (hP : PtOfInt) : CMIntegrality := by
  intro L l _ hl ι lam hlam h2 h3 hD z N hN hlN hNz hz
  have hμ0 : ι.symm lam ≠ 0 := by simpa using hlam
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hμ0
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  have hιc : ι (ι.symm lam)⁻¹ = lam⁻¹ := by simp
  have hg2' : ι (F.scalePair L (ι.symm lam)⁻¹ hc).g₂ = lam ^ 4 * ι L.g₂ := by
    rw [hg2, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
  have hg3' : ι (F.scalePair L (ι.symm lam)⁻¹ hc).g₃ = lam ^ 6 * ι L.g₃ := by
    rw [hg3, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
  have hInt : IntCurve (curveL l (F.scalePair L (ι.symm lam)⁻¹ hc) ι) := by
    unfold curveL
    rw [hg2', hg3']
    exact ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hcz : (ι.symm lam)⁻¹ * z ∉ (F.scalePair L (ι.symm lam)⁻¹ hc).lattice := by
    rw [hmem, inv_mul_cancel_left₀ hc]; exact hz
  have hNcz : (N : ℂ) * ((ι.symm lam)⁻¹ * z) ∈ (F.scalePair L (ι.symm lam)⁻¹ hc).lattice := by
    rw [hmem, mul_left_comm, inv_mul_cancel_left₀ hc]; exact hNz
  obtain ⟨hx, hy⟩ := hP l (F.scalePair L (ι.symm lam)⁻¹ hc) ι hInt _ N hN hlN hNcz hcz
  have hΔ : (curveL l (F.scalePair L (ι.symm lam)⁻¹ hc) ι).Δ ≠ 0 := by
    intro h0
    have := hInt.2.2.2.2.2
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [ScaledModelNorms.px_ptOf l _ ι hΔ _ hcz, hwp, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv] at hx
  rw [ScaledModelNorms.py_ptOf l _ ι hΔ _ hcz, ScaledModelNorms.dwp_scale L _ hc, norm_div, ScaledModelNorms.norm_two l hl, div_one,
    map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv] at hy
  exact ⟨hx, hy⟩

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.GeneralIntegrality
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations

namespace GeneratorMatrix

def blk (n : Type) (a : Fin 4) : n ↪ Fin 4 × n := ⟨fun i => (a, i), fun _ _ h => (Prod.mk.inj h).2⟩

theorem blk_apply {n : Type} (a b : Fin 4) (μ : n →₀ ℕ) (i : n) :
    Finsupp.embDomain (blk n a) μ (b, i) = if a = b then μ i else 0 := by
  split_ifs with h
  · subst h
    exact Finsupp.embDomain_apply_self (blk n a) μ i
  · refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨j, hj⟩
    exact h (Prod.mk.inj hj).1

section Field

variable {K : Type} [Field K] {n : Type}

theorem tensor4_eq_rename (f : MvPowerSeries n K) :
    tensor4 f = ∏ a, MvPowerSeries.rename (blk n a) f := by
  unfold tensor4
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem tensor4_mul (f g : MvPowerSeries n K) : tensor4 (f * g) = tensor4 f * tensor4 g := by
  rw [tensor4_eq_rename, tensor4_eq_rename, tensor4_eq_rename, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => map_mul _ _ _

theorem coeff_tensor4 (f : MvPowerSeries n K) (ν : n →₀ ℕ) :
    MvPowerSeries.coeff (∑ a, Finsupp.embDomain (blk n a) ν) (tensor4 f) =
      MvPowerSeries.coeff ν f ^ 4 := by
  classical
  rw [tensor4_eq_rename, MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun a => Finsupp.embDomain (blk n a) ν)]
  · simp
  · intro L hL hne
    by_contra h0
    apply hne
    rw [Finset.mem_finsuppAntidiag] at hL
    have hr : ∀ a, ∃ μ : n →₀ ℕ, L a = Finsupp.embDomain (blk n a) μ := by
      intro a
      by_contra hc
      apply h0
      refine Finset.prod_eq_zero (Finset.mem_univ a) (MvPowerSeries.coeff_rename_eq_zero _ _ ?_)
      rintro ⟨μ, hμ⟩
      exact hc ⟨μ, by rw [Finsupp.embDomain_eq_mapDomain, hμ]⟩
    choose μ hμ using hr
    have hμν : ∀ b, μ b = ν := by
      intro b
      ext i
      have := DFunLike.congr_fun hL.1 (b, i)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, hμ, blk_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      exact this
    ext1 a
    rw [hμ, hμν]
    rfl
  · intro h
    exact absurd (by simp [Finset.mem_finsuppAntidiag]) h

end Field

section Lin

variable {K : Type} [Field K] {O m : Type} [CommRing O] [Fintype m] {l linv : PowerSeries K}

theorem cc_matCoord (h : IsLogPair l linv) (τ : O →+* K) (γ : Matrix m m O) (w : m) :
    MvPowerSeries.constantCoeff (matCoord l linv τ γ w) = 0 :=
  Formalism.L2.Th1.C.Pts.constantCoeff_flin h _ fun _ => MvPowerSeries.constantCoeff_X _

theorem matCoord_comp (h : IsLogPair l linv) (τ : O →+* K) (γ δ : Matrix m m O) (w : m) :
    MvPowerSeries.subst (matCoord l linv τ δ) (matCoord l linv τ γ w) =
      matCoord l linv τ (γ * δ) w := by
  have hδ0 := cc_matCoord h τ δ
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ0
  have hL : ∀ j, PowerSeries.subst (matCoord l linv τ δ j) l =
      ∑ k, MvPowerSeries.C (τ (δ j k)) *
        PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries m K) l := fun j =>
    Formalism.L2.Th1.C.Pts.l_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  conv_lhs => rw [matCoord, Formalism.L2.Th1.C.flin]
  rw [Formalism.L2.Th1.C.Pts.substMv_subst
    (Formalism.L2.Th1.C.Pts.constantCoeff_sum_l h _ fun _ => MvPowerSeries.constantCoeff_X _) hδ0]
  conv_rhs => rw [matCoord, Formalism.L2.Th1.C.flin]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  have h1 : ∀ j, MvPowerSeries.substAlgHom hs (MvPowerSeries.C (τ (γ w j)) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l) =
      ∑ k, MvPowerSeries.C (τ (γ w j * δ j k)) *
        PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries m K) l := by
    intro j
    rw [map_mul, MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_C,
      Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X j) hδ0,
      MvPowerSeries.subst_X hs, hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, mul_assoc]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum, map_sum, Finset.sum_mul]

theorem matCoord_one [DecidableEq m] (h : IsLogPair l linv) (τ : O →+* K) (w : m) :
    matCoord l linv τ (1 : Matrix m m O) w = MvPowerSeries.X w := by
  rw [matCoord, Formalism.L2.Th1.C.flin, Finset.sum_eq_single w]
  · rw [Matrix.one_apply_eq, map_one, map_one, one_mul]
    exact Formalism.L2.Th1.C.Pts.subst_linv_l h (MvPowerSeries.constantCoeff_X w)
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, map_zero, map_zero, zero_mul]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

end Lin

section Exp

variable {K : Type} [NormedField K] [CharZero K] {n : Type} [Fintype n]

theorem tensor4_exp {ph : PowerSeries K} (hph : PowerSeries.constantCoeff ph = 0) :
    tensor4 (mvExp (phSum ph : MvPowerSeries n K)) =
      mvExp (phSum ph : MvPowerSeries (Fin 4 × n) K) := by
  have h1 : ∀ a : Fin 4, MvPowerSeries.subst
      (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K))
      (mvExp (phSum ph : MvPowerSeries n K)) = mvExp (∑ i, at1 (a, i) ph) := by
    intro a
    have h0 : ∀ i : n, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K) = 0 :=
      fun i => MvPowerSeries.constantCoeff_X _
    have h2 : MvPowerSeries.subst (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K))
        (phSum ph : MvPowerSeries n K) = ∑ i, at1 (a, i) ph := subst_phSum ph h0
    rw [← h2]
    exact Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp (cc_phSum hph) h0
  unfold tensor4
  rw [Finset.prod_congr rfl fun a _ => h1 a]
  have h3 : (phSum ph : MvPowerSeries (Fin 4 × n) K) = ∑ a : Fin 4, ∑ i : n, at1 (a, i) ph := by
    unfold phSum
    exact Fintype.sum_prod_type _
  rw [h3]
  refine (Formalism.L2.Th1.C.mvExp_sum _ _ fun a _ => ?_).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => constantCoeff_inVar_eq_zero _ hph

end Exp

end GeneratorMatrix

open GeneratorMatrix

theorem fourth_power : FourthPower := by
  intro K _ _ n f h ν
  have h1 := h (∑ a, Finsupp.embDomain (blk n a) ν)
  rw [coeff_tensor4, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1

theorem GeneralIntOf_of (hF : FourthPower) (hU : Formalism.L2.Th1.C.UnitaryInv) (hP : ProdInt)
    (hS : SubstExpInt) (hC : CongIffSimeq) : GeneralIntOf := by
  intro K _ _ _ R hR l linv ph hFr O _ _ τ hEnd hBin hF1 hN hA n _ _ Θ γ hγ hK
  obtain ⟨κ, _, r, V, hr, hV, hEq⟩ := hK
  obtain ⟨hlp, hFG, hph⟩ := hFr
  have hγδ : γ * γ.conjTranspose = 1 := mul_eq_one_comm.1 hγ
  have hδ : γ.conjTranspose.conjTranspose * γ.conjTranspose = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hγδ
  have hpt : ∀ w, IsPt R (matCoord l linv τ γ.conjTranspose w) := fun w =>
    Formalism.L2.Th1.C.Pts.isPt_flin hlp hFG (fun _ => hEnd _) fun _ => isPt_X _
  obtain ⟨h1, h2⟩ := hP K κ (Fin 4 × n) ph r V hph hr hV
  obtain ⟨h3, h4, h5⟩ := hS K (Fin 4 × n) (Fin 4 × n) (matCoord l linv τ γ.conjTranspose)
    (fun i => (hpt i).1) (fun i => (integral_iff hR _).2 (hpt i).2) (phSum ph) (thetaProd r V)
    (cc_phSum hph) h2
  have hT : tensor4 Θ =
      mvExp (-(MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph))) *
        MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (thetaProd r V) := by
    rw [← h3, ← h1, ← hEq, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_matCoord hlp τ γ))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_matCoord hlp τ γ.conjTranspose))]
    have hX : (fun w => MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose)
        (matCoord l linv τ γ w)) = MvPowerSeries.X := by
      funext w
      rw [matCoord_comp hlp, hγδ, matCoord_one hlp]
    rw [hX, MvPowerSeries.subst_self]
    rfl
  have hcong : Formalism.L2.Th1.C.Cong R (phSum ph : MvPowerSeries (Fin 4 × n) K)
      (MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph)) := by
    rw [subst_phSum ph fun i => (hpt i).1]
    exact Formalism.L2.Th1.C.Calc.cong_symm (hU K R l linv ph ⟨hlp, hFG, hph⟩ O τ hEnd hBin hF1 hN hA
      (Fin 4 × n) γ.conjTranspose hδ (Fin 4 × n) MvPowerSeries.X fun _ => isPt_X _)
  have hsim := ((hC K R hR _ _ _).1 hcong).2
  apply hF
  rw [tensor4_mul, tensor4_exp hph, hT, ← mul_assoc]
  have hadd : mvExp (phSum ph : MvPowerSeries (Fin 4 × n) K) *
      mvExp (-(MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph))) =
      mvExp ((phSum ph : MvPowerSeries (Fin 4 × n) K) -
        MvPowerSeries.subst (matCoord l linv τ γ.conjTranspose) (phSum ph)) :=
    (Formalism.L2.Th1.C.mvExp_sub (cc_phSum hph) h5).symm
  rw [hadd]
  exact (integral_iff hR _).2 (Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_mul ((integral_iff hR _).1 hsim)
    ((integral_iff hR _).1 h4))

theorem general_integrality : GeneralIntOf :=
  GeneralIntOf_of fourth_power Formalism.L2.Th1.C.unitaryInv product_integral subst_exp_integral
    congruence_iff_simeq

end Formalism.L2.Th1.E
end
end

