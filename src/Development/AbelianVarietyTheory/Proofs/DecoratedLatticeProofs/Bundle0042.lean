module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InSuppMulLeft
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.DatumEigenLeft

open GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']


omit [Fintype D] [DecidableEq D] in
theorem inSupp_mul_left {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D') k}
    (hj : j ∈ parahoric k A D') : InSupp (j.val * x) ∧
      valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (j.val * x) i l ∈ 𝒪[k] := fun i l => by
    rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hxi m l)
  have hcong : valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hxi _ _)
    · simp only [toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hJ _ _) (hxl _ _)
  have hd1 : valuation k (j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, mul_one, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hxi _ _) (hl _ _)
    · exact val_mul_lt (hJ _ _) (hxl _ _)

end GlobalTheory.DatumEigenLeft

namespace GlobalTheory.DatumEigenLeft
open GlobalTheory.DatumEigen

theorem omTwo_datum_inv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → ∀ j ∈ parahoric k A D', ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D') (A ⊕ D') k).toBlocks₂₂.det → omTwo μS μT (1 : GL (A ⊕ D) k) j (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) = (ξ d : ℂ) • (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ξ μS μT hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hμ _ hdetv
    rwa [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, MonoidHom.inv_apply,
    map_one, inv_one, Units.val_one, one_mul, Real.one_rpow, Complex.ofReal_one, mul_one, inv_inv]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one, Units.val_mul,
    hμj]
  have hT : (μT (GeneralLinearGroup.det j) : ℂ) ≠ 0 := Units.ne_zero _
  have e1 : ((ξ (GeneralLinearGroup.det j) : ℂ) * (((μT (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ)) *
      ((μT (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x)) =
      (ξ (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [Units.val_inv_eq_inv_val]; field_simp
  rw [e1]
  have hx : x = j.val * ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  generalize (j⁻¹ : GL (A ⊕ D') k).val * x = y at hx ⊢
  subst hx
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hy : InSupp y
  · obtain ⟨hs, hc⟩ := inSupp_mul_left hy hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (u * Units.mk0 _ hy.det_ne) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hu, Units.val_mk0, Units.val_mk0, hy.2.1, h11, mul_one]) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dite_eq_left hs, dite_eq_left hy, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, inv_inv, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul]
    ring
  · have hs : ¬ InSupp (j.val * y) := fun hs => by
      have := (inSupp_mul_left hs (inv_mem hj)).1
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
      exact hy this
    rw [dite_eq_right hs, dite_eq_right hy, mul_zero, mul_zero]

end GlobalTheory.DatumEigenLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricDoubleCosetValuation
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCap

theorem val_mul_lt_left {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (c : Matrix X Y k)
    (w : Matrix Y Z k) (hc : ∀ i j, valuation k (c i j) < 1) (hw : ∀ i j, valuation k (w i j) ≤ 1) :
    ∀ i j, valuation k ((c * w) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (hw l j)) (hc i l)

theorem val_mul_lt_right {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (w : Matrix X Y k)
    (c : Matrix Y Z k) (hw : ∀ i j, valuation k (w i j) ≤ 1) (hc : ∀ i j, valuation k (c i j) < 1) :
    ∀ i j, valuation k ((w * c) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hw i l)) (hc l j)

theorem toBlocks₂₁_mul_mul {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (P E Q : Matrix (A ⊕ D) (A ⊕ D) k) (hP : P.toBlocks₂₁ = 0) (hE : E.toBlocks₂₁ = 0)
    (hQ : Q.toBlocks₂₁ = 0) : (P * E * Q).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks E, ← fromBlocks_toBlocks Q, hP, hE, hQ]
  simp [fromBlocks_multiply]

theorem lowUni_mul_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (fromBlocks 1 0 X 1 * M).toBlocks₂₁ = X * M.toBlocks₁₁ + M.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

theorem mul_lowUni_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (M * fromBlocks 1 0 X 1).toBlocks₂₁ = M.toBlocks₂₁ + M.toBlocks₂₂ * X := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

theorem lowerUni_mem_cap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (ν : Matrix D A k)
    (m : GL D k), g.1 = fromBlocks 1 0 ν m.1 →
    (∃ x y, ∃ j ∈ parahoric k A D, ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j') →
    ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧
      ν = ν₁ + m.1 * ν₂ := by
  intro k _ _ _ _ A D _ _ _ _ g ν m hg ⟨x, y, j, hj, j', hj', he⟩
  obtain ⟨⟨u, hu, hua⟩, -, hc, -⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j.1).1 ⟨j, hj, rfl⟩
  obtain ⟨-, -, hc', ⟨u', hu', hud⟩⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j'.1).1 ⟨j', hj', rfl⟩
  have hui := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u⁻¹).1).1 ⟨u⁻¹, inv_mem hu, rfl⟩).1
  have hui' := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u'⁻¹).1).1 ⟨u'⁻¹, inv_mem hu', rfl⟩).1
  set ν₁ := j.1.toBlocks₂₁ * (u⁻¹).1
  set ν₂ := (u'⁻¹).1 * j'.1.toBlocks₂₁
  refine ⟨ν₁, ν₂, val_mul_lt_left _ _ hc hui, val_mul_lt_right _ _ hui' hc', ?_⟩
  have hP : (fromBlocks 1 0 (-ν₁) 1 * j.1).toBlocks₂₁ = 0 := by
    have e1 : ν₁ * u.1 = j.1.toBlocks₂₁ := by simp only [ν₁, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [lowUni_mul_toBlocks₂₁, ← hua, Matrix.neg_mul, e1, neg_add_cancel]
  have hQ : (j'.1 * fromBlocks 1 0 (-ν₂) 1).toBlocks₂₁ = 0 := by
    have e2 : u'.1 * ν₂ = j'.1.toBlocks₂₁ := by simp only [ν₂, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [mul_lowUni_toBlocks₂₁, ← hud, Matrix.mul_neg, e2, add_neg_cancel]
  have hE : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1.toBlocks₂₁ = 0 := by
    rw [val_emb₂]
    simp
  have key := toBlocks₂₁_mul_mul _ _ _ hP hE hQ
  have h2 : fromBlocks 1 0 (-ν₁) 1 * j.1 * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1 *
      (j'.1 * fromBlocks 1 0 (-ν₂) 1) = fromBlocks 1 0 (-ν₁) 1 * g.1 * fromBlocks 1 0 (-ν₂) 1 := by
    rw [he]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [h2, hg] at key
  simp [fromBlocks_multiply] at key
  rw [← sub_eq_zero, ← key]
  abel

end GlobalTheory.ParHeckeCap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScaleLargeThree
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem scale_large_three (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    Real.log (4 * s.x) ≤ s.L ∧ 8 ≤ s.X' ∧ 2 ≤ s.x := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1/2) * x ^ eps := by
    have := (isLittleO_log_rpow_atTop he).bound (c := 1/2) (by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hp : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hp] at hx
    exact hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log 4 ≤ (1/2) * x ^ eps := by
    have := (tendsto_rpow_atTop he).eventually_ge_atTop (2 * Real.log 4)
    filter_upwards [this] with x hx
    linarith
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, (3 : ℝ) ≤ x ^ (eps / 3) :=
    (tendsto_rpow_atTop (by linarith : 0 < eps / 3)).eventually_ge_atTop 3
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (h1.and (h2.and (h3.and (Filter.eventually_ge_atTop (2 : ℝ)))))
  refine ⟨x0, fun s hs hx => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 s.x hx
  have hxpos : 0 < s.x := by linarith
  refine ⟨?_, ?_, a4⟩
  · show Real.log (4 * s.x) ≤ s.x ^ s.eps
    rw [Real.log_mul (by norm_num) hxpos.ne', hs]
    linarith
  · show 8 ≤ Real.exp (s.x ^ (s.eps / 3))
    rw [hs]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h8 : (8 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he1 3]
    exact h8.trans (Real.exp_le_exp.2 a3)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SubstCongrModPrimeOfIntegralDerivativeStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 → ∀ (f : K⟦X⟧), CoefLe 1 (PowerSeries.derivative f) → ∀ (s : Type) (A B : MvPowerSeries s K), MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 → (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) → ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l hl hlt f hf s A B hA0 hB0 hA hB hAB m
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero hA0
  have hsB : HasSubst B := HasSubst.of_constantCoeff_zero hB0
  have hterm : ∀ d : ℕ, ‖coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hcong := Formalism.LT.PowCongr_valid K s l hl A B hA hB 1 le_rfl
      (by intro e; simpa using hAB e) (padicValNat l d) (d / l ^ padicValNat l d) m
    have hdecomp : l ^ padicValNat l d * (d / l ^ padicValNat l d) = d :=
      Nat.mul_div_cancel' (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [hdecomp, norm_pow, pow_add, pow_one] at hcong
    have hnd : ‖(d : K)‖ = ‖(l : K)‖ ^ padicValNat l d :=
      Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hl hlt hd.ne'
    have hder : ‖coeff d f‖ * ‖(d : K)‖ ≤ 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := hf k
      rw [coeff_derivative, norm_mul] at this
      simpa using this
    rw [norm_mul]
    calc ‖coeff d f‖ * ‖MvPowerSeries.coeff m (A ^ d - B ^ d)‖
        ≤ ‖coeff d f‖ * (‖(l : K)‖ * ‖(d : K)‖) := by
          rw [hnd]; exact mul_le_mul_of_nonneg_left hcong (norm_nonneg _)
      _ = ‖(l : K)‖ * (‖coeff d f‖ * ‖(d : K)‖) := by ring
      _ ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left hder (norm_nonneg _)
      _ = ‖(l : K)‖ := mul_one _
  rw [map_sub, coeff_subst hsA, coeff_subst hsB,
    ← finsum_sub_distrib (coeff_subst_finite hsA f m) (coeff_subst_finite hsB f m)]
  have heq : (fun d : ℕ => coeff d f • MvPowerSeries.coeff m (A ^ d) - coeff d f • MvPowerSeries.coeff m (B ^ d))
      = fun d => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d) := by
    funext d; rw [map_sub, smul_eq_mul, smul_eq_mul, mul_sub]
  have hfin : (Function.support fun d : ℕ => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)).Finite := by
    rw [← heq]
    exact ((coeff_subst_finite hsA f m).union (coeff_subst_finite hsB f m)).subset
      (Function.support_sub _ _)
  rw [heq, finsum_eq_sum _ hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => hterm d
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNegIndic
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.TorusRightScalar

theorem det_mtor' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]

theorem sum_neg_indic {D : Type} [Fintype D] [DecidableEq D] (s : Finset D) :
    ∑ i, (-indic s) i = -(s.card : ℤ) := by
  simp [indic, Finset.sum_neg_distrib, Finset.sum_ite_mem]

theorem torusRight : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μT * ξ⁻¹) → ∀ (s : Finset D) (j : GL (A ⊕ D) k), j ∈ parahoric k A D → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (j * mtor ϖ (-indic s)) (1 : GL (A ⊕ D') k) u y = (((ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * (μT ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D')) * u (y * (j * mtor ϖ (-indic s)).1) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hun s j hj u y
  have hjK : j ∈ KO k (A ⊕ D) := (mem_parahoric.1 hj).1
  have hn1 : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hjK
  have hv1 : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hn1
  have hxi : μT (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hun _ hv1
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdet : GeneralLinearGroup.det (j * mtor ϖ (-indic s)) =
      GeneralLinearGroup.det j * ϖ ^ (-(s.card : ℤ)) := by
    rw [map_mul, det_mtor', sum_neg_indic]
  have hq0 : (0 : ℝ) < resCard k := by
    have q1 : 1 < Nat.card 𝓀[k] := Finite.one_lt_card
    unfold resCard; exact_mod_cast (lt_trans one_pos q1)
  have hnabs : nabs k (GeneralLinearGroup.det (j * mtor ϖ (-indic s))) = (resCard k : ℝ) ^ s.card := by
    rw [map_mul, show nabs k (GeneralLinearGroup.det j * GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) =
      nabs k (GeneralLinearGroup.det j) * nabs k (GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) by
        simp [nabs, map_mul], hn1, one_mul, mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]
    simp [indic, Finset.sum_ite_mem]
  have hpow : ((resCard k : ℝ) ^ s.card) ^ ((Fintype.card (A ⊕ D') : ℝ) / 2) =
      (Real.sqrt (resCard k)) ^ (s.card * (Fintype.card A + Fintype.card D')) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
      ← Real.rpow_mul hq0.le, Fintype.card_sum]
    congr 1
    push_cast
    ring
  simp only [omTwo, om, map_one, inv_one, Units.val_one, one_smul, Matrix.one_mul, hnabs, hpow]
  have h1 : nabs k 1 = 1 := by simp [nabs]
  rw [h1, Real.one_rpow, hdet, map_mul, map_zpow, MonoidHom.inv_apply, MonoidHom.inv_apply, hxi]
  push_cast
  simp only [_root_.zpow_neg, zpow_natCast]
  rw [inv_pow, inv_inv]
  ring

end GlobalTheory.TorusRightScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt
section
open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem hsNormSq_eq_sum_stdBasis {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : V →L[ℂ] H) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem sum_norm_sq_le_hsNormSq {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V) (hv : Orthonormal ℂ v) :
    ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  set e := stdOrthonormalBasis ℂ V with he
  set f := stdOrthonormalBasis ℂ H
  have key : ∀ (x : V) (y : H), ‖⟪y, A x⟫_ℂ‖ = ‖⟪x, (ContinuousLinearMap.adjoint A) y⟫_ℂ‖ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
  calc ∑ i, ‖A (v i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪f j, A (v i)⟫_ℂ‖ ^ 2 := by
        simp_rw [f.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪v i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ ≤ ∑ j, ‖(ContinuousLinearMap.adjoint A) (f j)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hv.sum_inner_products_le _
    _ = ∑ j, ∑ i, ‖⟪e i, (ContinuousLinearMap.adjoint A) (f j)⟫_ℂ‖ ^ 2 := by
        simp_rw [e.sum_sq_norm_inner_right]
    _ = ∑ i, ∑ j, ‖⟪f j, A (e i)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [key]
    _ = hsNormSq A := by
        rw [hsNormSq_eq_sum_stdBasis, ← he]
        simp_rw [f.sum_sq_norm_inner_right]

end GlobalTheory
end

