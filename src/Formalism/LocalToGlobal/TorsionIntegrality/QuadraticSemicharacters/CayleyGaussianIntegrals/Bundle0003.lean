module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegral
section
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

theorem gauss_plane (l : ℂ) (hl : 0 < l.re) :
    Integrable (fun z : ℂ => Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ z : ℂ, Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2) = l⁻¹ := by
  have hl0 : l ≠ 0 := fun h => by simp [h] at hl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb : 0 < ((Real.pi : ℂ) * l).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos hl
  refine ⟨?_, ?_⟩
  · have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 (0 : ℂ)
    simpa using this
  · rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) hb, Complex.finrank_real_complex]
    rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    field_simp

theorem gauss_pi {n : Type*} [Fintype n] (l : n → ℂ) (hl : ∀ i, 0 < (l i).re) :
    Integrable (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ w : n → ℂ, Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = (∏ i, l i)⁻¹ := by
  have hfun : (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) =
      fun w => ∏ i, Complex.exp (-((Real.pi : ℂ) * l i) * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact Integrable.fintype_prod
      (f := fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2))
      (fun i => (gauss_plane (l i) (hl i)).1)
  · rw [integral_fintype_prod_volume_eq_prod
      (fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2)),
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (gauss_plane (l i) (hl i)).2

theorem haar_transfer {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {n : Type*} [Fintype n] (Φ : (n → ℂ) ≃ₗ[ℂ] V) :
    ∃ κ : ℝ, ∀ f : V → ℂ, (Integrable (fun w => f (Φ w)) → Integrable f μ) ∧
      ∫ z, f z ∂μ = (κ : ℂ) * ∫ w, f (Φ w) := by
  classical
  let Ψ : (n → ℂ) ≃L[ℂ] V := Φ.toContinuousLinearEquiv
  let ν : Measure V := Measure.map Ψ volume
  have hme : MeasurableEmbedding Ψ := Ψ.toHomeomorph.measurableEmbedding
  obtain ⟨c, hμ⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  subst hμ
  refine ⟨(c : ℝ), fun f => ⟨fun hf => ?_, ?_⟩⟩
  · apply Integrable.smul_measure_nnreal
    rw [hme.integrable_map_iff]
    exact hf
  · rw [integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul]
    try rfl

theorem cayleyGaussianIntegral : GaussQuad := by
  intro V _ _ _ _ _ μ _ H hH hP δ Ae hδ hAe
  classical
  obtain ⟨b, l, hb, hbl, hl⟩ := unitary_diag H hH hP δ Ae hδ hAe
  obtain ⟨κ, hκ⟩ := haar_transfer μ b.equivFun.symm
  have hq : (fun w => gq H Ae (b.equivFun.symm w)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b l (Ae : V →ₗ[ℂ] V) hb hbl w
    simp only [LinearEquiv.coe_coe] at h1
    unfold gq
    rw [h1]
  have hw : (fun w => ((wt H (b.equivFun.symm w) : ℝ) : ℂ)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b (fun _ => (1 : ℂ)) LinearMap.id hb (fun i => by simp) w
    simp only [LinearMap.id_apply] at h1
    have hs : (∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp
    unfold wt
    rw [h1, hs, Complex.ofReal_re, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  have hgq := gauss_pi l hl
  have hgw := gauss_pi (n := Fin (Module.finrank ℂ V)) (fun _ => (1 : ℂ)) (fun _ => by simp)
  rw [← hq] at hgq
  rw [← hw] at hgw
  refine ⟨(hκ _).1 hgq.1, ?_⟩
  rw [(hκ (gq H Ae)).2, hgq.2, ← integral_complex_ofReal, (hκ (fun z => ((wt H z : ℝ) : ℂ))).2, hgw.2,
    det_of_diag b l (Ae : V →ₗ[ℂ] V) hbl]
  simp [div_eq_mul_inv]

end Formalism.L2.Th1.H
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section SlopeTestRemainingChoices

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem herm_sub_swap (H : Sesq V) (hH : IsHerm H) (x y : V) :
    H x y - H y x = 2 * Complex.I * (altE H x y : ℂ) := by
  rw [hH x y, Complex.sub_conj, altE]
  push_cast
  ring

theorem altE_swap (H : Sesq V) (hH : IsHerm H) (x y : V) : altE H y x = -altE H x y := by
  simp only [altE, hH x y, Complex.conj_im]

theorem re_swap (H : Sesq V) (hH : IsHerm H) (x y : V) : (H y x).re = (H x y).re := by
  rw [hH x y, Complex.conj_re]

end SlopeTestRemainingChoices

theorem heisenbergMul : OpUMul := by
  intro V _ _ H hH x y F z
  have hs := herm_sub_swap H hH x y
  simp only [opU]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]
  congr 2
  simp only [map_add (f := _), LinearMap.add_apply]
  linear_combination (-(Real.pi : ℂ) / 2) * hs

theorem heisenbergComm : OpUComm := by
  intro V _ _ H hH F z
  refine ⟨by simp [opU], fun x y => ?_⟩
  have h1 := heisenbergMul V H hH x y F z
  have h2 := heisenbergMul V H hH y x F z
  rw [add_comm y x, altE_swap H hH] at h2
  rw [h1, h2, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem heisenbergIsometry : OpUIsom := by
  intro V W _ _ _ _ H H' g hg x G z
  simp only [opU, map_add (f := _)]
  rw [hg z x, hg x x]

theorem precompHeisenberg : PullOpU := by
  intro V _ _ H δ hδ x F z
  have h1 : H z (δ x) = H (δ.symm z) x := by
    have h := hδ (δ.symm z) x
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h
  have h2 : H (δ x) (δ x) = H x x := by
    have h := hδ x x
    simpa only [LinearEquiv.coe_coe] using h
  simp only [pullInv, opU, map_add (f := _), LinearEquiv.symm_apply_apply, h1, h2]

theorem semicharacterBasic : SemiCharBasic := by
  intro V _ _ H hH Λ α hα
  obtain ⟨hpm, hmul⟩ := hα
  have hA0 : ∀ x, altE H x x = 0 := fun x => Complex.conj_eq_iff_im.mp (hH x x).symm
  have h0 : α 0 = 1 := by
    have h := hmul 0 Λ.zero_mem 0 Λ.zero_mem
    rw [add_zero, hA0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
    rcases hpm 0 Λ.zero_mem with h' | h'
    · exact h'
    · rw [h'] at h; norm_num at h
  have hneg : ∀ x ∈ Λ, α (-x) = α x := by
    intro x hx
    have h := hmul x hx (-x) (Λ.neg_mem hx)
    have hA : altE H x (-x) = 0 := by
      have h' := hA0 x
      simp only [altE] at h' ⊢
      rw [map_neg, Complex.neg_im, h', neg_zero]
    rw [add_neg_cancel, h0, hA, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
    rcases hpm x hx with h1 | h1 <;> rcases hpm (-x) (Λ.neg_mem hx) with h2 | h2 <;>
      rw [h1, h2] at h ⊢ <;> try norm_num at h
  have hdual : Λ ≤ dualLat H Λ := by
    intro x hx
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)
    intro y hy
    have e1 := hmul x hx y hy
    have e2 := hmul y hy x hx
    rw [add_comm y x, altE_swap H hH] at e2
    have hxne : α x ≠ 0 := by rcases hpm x hx with h | h <;> rw [h] <;> norm_num
    have hyne : α y ≠ 0 := by rcases hpm y hy with h | h <;> rw [h] <;> norm_num
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE H x y : ℝ) : ℂ)) := by
      have h := e1.symm.trans e2
      rw [mul_comm (α y) (α x)] at h
      exact mul_left_cancel₀ (mul_ne_zero hxne hyne) h
    rw [Complex.exp_eq_exp_iff_exists_int] at he
    obtain ⟨n, hn⟩ := he
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
    push_cast at hn
    have h' : ((altE H x y : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero' ℂ) hpi)
      linear_combination hn
    exact_mod_cast h'
  exact ⟨h0, hneg, hdual⟩

theorem semicharacterHom : SemiHom := by
  intro V _ _ H hH Λ α hα x hx y hy F z
  have hU : opU H x (fun v => α y * opU H y F v) z = α y * opU H x (opU H y F) z := by
    simp only [opU]; ring
  have hd : x ∈ dualLat H Λ := (semicharacterBasic V H hH Λ α hα).2.2 hx
  obtain ⟨m, hm⟩ := (show ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ) from hd) y hy
  have hexp : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    rw [hm]
    push_cast
    ring
  rw [hU, heisenbergMul V H hH x y F z, hα.2 x hx y hy, hexp]
  ring

theorem heisenbergAnalytic : OpUAnalytic := by
  intro V _ _ _ H x F hF z _
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => H v x
      map_add' := fun a b => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c a => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hlin : AnalyticAt ℂ (fun v => H v x) z := (LinearMap.toContinuousLinearMap L).analyticAt z
  have hF' : AnalyticAt ℂ (fun v => F (v + x)) z :=
    AnalyticAt.comp (x := z) (f := fun v => v + x) (hF (z + x) (Set.mem_univ _))
      (analyticAt_id.add analyticAt_const)
  have hE : AnalyticAt ℂ
      (fun v => Complex.exp (-(Real.pi : ℂ) * H v x - (Real.pi : ℂ) * H x x / 2)) z :=
    ((analyticAt_const.mul hlin).sub analyticAt_const).cexp
  exact hF'.mul hE

theorem matH_apply {n : Type*} [Fintype n] (h : Matrix n n ℂ) (z w : n → ℂ) :
    matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j) := rfl

theorem matrixFormBasic : MatHBasic := by
  intro n _ h
  refine ⟨fun z w => rfl, fun hh x y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [matH_apply, matH_apply, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : conj (h i j) = h j i := by
    have h' := congrFun (congrFun hh j) i
    simpa [Matrix.conjTranspose_apply] using h'
  rw [hc]
  ring

theorem stdH_apply (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] (z w : n → ℂ) :
    stdH L n z w = ∑ i, Formalism.L2.Th1.F.herm L (z i) (w i) := by
  rw [stdH, matH_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply, Ne.symm hj]) (by simp)]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Formalism.L2.Th1.F.herm]
  ring

theorem standardFormBasic : StdHBasic := by
  intro L n _ _
  have harea := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos L
  refine ⟨stdH_apply L n, fun x y => ?_, fun x hx => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [stdH_apply, stdH_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have hi : ∀ i, Formalism.L2.Th1.F.herm L (x i) (x i) =
        ((Complex.normSq (x i) / Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
      intro i
      simp only [Formalism.L2.Th1.F.herm, Complex.mul_conj]
      push_cast
      ring
    rw [stdH_apply, Complex.re_sum]
    simp only [hi, Complex.ofReal_re]
    obtain ⟨i, hi0⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun j _ => div_nonneg (Complex.normSq_nonneg _) harea.le)
      ⟨i, Finset.mem_univ _, div_pos (Complex.normSq_pos.mpr hi0) harea⟩

theorem heisenbergStandard : OpUStd := by
  intro L n _ _ x f z
  simp only [opU, Formalism.L2.Th1.F.opU, prodFn, stdH_apply, Pi.add_apply]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]

theorem matrixForm_fourfoldBlock {n : Type*} [Fintype n] (h : Matrix n n ℂ) (z w : Fin 4 × n → ℂ) :
    matH (blk4 h) z w = ∑ a, matH h (slice a z) (slice a w) := by
  simp only [matH_apply, slice, blk4, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem heisenbergFourfold : OpUBlk4 := by
  intro n _ h
  refine ⟨matrixForm_fourfoldBlock h, fun x θ z => ?_⟩
  simp only [opU, matrixForm_fourfoldBlock]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  rfl

end Formalism.L2.Th1.H
end
end

