module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LeadTDerCols
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ShapeFromFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.VarsZeroOfSupported
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ShapeProdVarMatNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauBFin
section
namespace PI.FJMX

theorem minorProductDiagonal : PI.FJMB.HypShape := fun _ _ ι hι α hα =>
  ⟨shapeProd_hwb ι hι _, shapeProd_diag ι hι α hα⟩

end PI.FJMX
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHighestWeightOfShape
section
namespace PI.FJMB

theorem cauchy_highest_weight_of_shape (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  refine cauchyHW_of ?_ hS hD hF
  intro σ m n ι hι α P hP hrow hdeg
  exact PI.FJMF.block_degree_antitone σ m n ι hι α P hP hrow hdeg

end PI.FJMB
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.DiagonalImageBlockFree
section
noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

variable {σ : Type*}

theorem cd_mono_factor {m : ℕ} (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (e : σ →₀ ℕ) :
    aeval (killS (offD ι)) (monomial e (1 : ℂ)) =
      (∏ i, X (ι (i, i)) ^ (∑ k : Fin m, e (ι (i, k)))) * aeval (diagOne' ι) (monomial e (1 : ℂ)) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, map_one, one_mul, one_mul]
  by_cases hoff : ∃ v ∈ e.support, v ∈ offD ι
  · obtain ⟨v, hv, hvo⟩ := hoff
    have h1 : (e.prod fun v k => killS (offD ι) v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [killS, if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    have h2 : (e.prod fun v k => diagOne' ι v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [diagOne', if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    rw [h1, h2, mul_zero]
  · push_neg at hoff
    have hsum : ∀ i, ∑ k : Fin m, e (ι (i, k)) = e (ι (i, i)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        by_contra hne
        exact hoff (ι (i, k)) (Finsupp.mem_support_iff.mpr hne) ⟨i, k, rfl, fun h => hk (Fin.ext h).symm⟩
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hsum]
    have hL : (e.prod fun v k => killS (offD ι) v ^ k) = ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [killS, if_neg (hoff v hv)]
    have hR : (e.prod fun v k => diagOne' ι v ^ k) =
        ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [diagOne', if_neg (hoff v hv)]
      split_ifs <;> simp
    have hsplit : ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v =
        (∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1) *
          ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs <;> simp
    have hF : ∏ v ∈ e.support.filter (fun v => ∃ i k, ι (i, k) = v ∧ (i : ℕ) = k), (X v : MvPolynomial σ ℂ) ^ e v =
        ∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1 := by
      rw [Finset.prod_filter]
    have hinj : Function.Injective (fun i : Fin m => ι (i, i)) := fun a b h => (Prod.mk.inj (hι h)).1
    have himg : ∏ i, (X (ι (i, i)) : MvPolynomial σ ℂ) ^ e (ι (i, i)) =
        ∏ v ∈ Finset.univ.image (fun i : Fin m => ι (i, i)), (X v : MvPolynomial σ ℂ) ^ e v := by
      rw [Finset.prod_image (fun a _ b _ h => hinj h)]
    rw [hL, hR, hsplit, ← hF, himg]
    congr 1
    apply Finset.prod_subset
    · intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨i, k, hik, hk⟩ := hv.2
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [← hik, ← Fin.ext hk]
    · intro v hv hvf
      rw [Finset.mem_image] at hv
      obtain ⟨i, _, rfl⟩ := hv
      have h0 : e (ι (i, i)) = 0 := by
        by_contra hne
        exact hvf (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, i, i, rfl, rfl⟩)
      rw [h0, pow_zero]

theorem diagonal_hypothesis : HypDiag := by
  intro σ m ι hι α P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hm : MvPolynomial.monomial e (P.coeff e) = MvPolynomial.C (P.coeff e) * MvPolynomial.monomial e 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, map_mul, map_mul, cd_mono_factor ι hι e]
  have hs : ∀ i, ∑ k : Fin m, e (ι (i, k)) = α i := hP e he
  simp only [hs, MvPolynomial.aeval_C]
  ring

theorem diagonal_image_block_free : HypFree := by
  intro σ m n ι hι P
  have hC : ∀ c : ℂ, ∀ e ∈ (MvPolynomial.C c : MvPolynomial σ ℂ).support, ∀ x, e (ι x) = 0 := by
    intro c e he x
    rw [MvPolynomial.C_apply] at he
    have h0 := MvPolynomial.support_monomial_subset he
    rw [Finset.mem_singleton] at h0
    rw [h0]
    rfl
  have hadd : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q + R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact hQ e h x
    · exact hR e h x
  have hmul : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q * R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul Q R he)
    rw [Finsupp.add_apply, hQ a ha x, hR b hb x]
  have hgen : ∀ w, ∀ e ∈ (diagOne' ι w).support, ∀ x, e (ι x) = 0 := by
    intro w
    unfold diagOne'
    split_ifs with h1 h2
    · simpa using hC 0
    · simpa using hC 1
    · intro e he x
      have hne : w ≠ ι x := by
        rintro rfl
        obtain ⟨i, k⟩ := x
        by_cases hik : (i : ℕ) = k
        · exact h2 ⟨i, k, rfl, hik⟩
        · exact h1 ⟨i, k, rfl, hik⟩
      rw [MvPolynomial.support_X, Finset.mem_singleton] at he
      rw [he, Finsupp.single_apply, if_neg hne]
  induction P using MvPolynomial.induction_on
  next a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    exact hC a
  next p q hp hq =>
    rw [map_add (f := _)]
    exact hadd _ _ hp hq
  next p w hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact hmul _ _ hp (hgen w)

end PI.FJMB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.FockJointMultOfCauchy
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

theorem minHyp_of_mem {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ JH p q r s μ μ') (h0 : P ≠ 0) : MinHyp p q r s μ μ' P := by
  obtain ⟨⟨d1, hd1, hP1⟩, ⟨d2, hd2, hP2⟩⟩ := PI.FJMF.minimal_degree_joint p q r s μ μ' P hP h0
  have h12 : d1 = d2 :=
    ((mem_homogeneousSubmodule _ _).1 hP1).inj_right ((mem_homogeneousSubmodule _ _).1 hP2) h0
  subst h12
  exact ⟨hP, h0, d1, hd1, hd2, hP1⟩

theorem shapeOf_of_cauchy (hC : CauchyHW) : ShapeOf := by
  intro p q r s μ μ' P hP h0
  have hM := minHyp_of_mem hP h0
  exact shape_from_facts p q r s μ μ'
    (PI.FJMA.line_of hC PI.FJMS.hypothesis_first_cover PI.FJMS.hypothesis_second_cover PI.FJMS.hypothesis_third_cover PI.FJMS.hypothesis_fourth_cover
      PI.FJMS.cover_by_blocks p q r s μ μ' P hM).1
    (PI.FJMS.segs_of hM) (PI.FJMS.intFacts_of hM)

theorem rankLe_of_cauchy (hC : CauchyHW) : RankLe := by
  intro p q r s μ μ' _
  refine ⟨vLine p q r s μ μ', fun P hP => ?_⟩
  by_cases h0 : P = 0
  · rw [h0]; exact Submodule.zero_mem _
  · obtain ⟨c, hc⟩ := (PI.FJMA.line_of hC PI.FJMS.hypothesis_first_cover PI.FJMS.hypothesis_second_cover PI.FJMS.hypothesis_third_cover
      PI.FJMS.hypothesis_fourth_cover PI.FJMS.cover_by_blocks p q r s μ μ' P (minHyp_of_mem hP h0)).2
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, C_mul']⟩

theorem fockJointMult_of_cauchy (hC : CauchyHW) : PI.FockDegreeTwoParts.JointMult := jointMult_of
    (exist_of PI.FJMD.shapeVector_ne_zero (PI.FJMD.vecJ_of jointHarmonicsIffLaplacians) (PI.FJMX.vecHW1_of leftDiagonalActionFormula leftOffDiagonalActionFormula)
      (PI.FJMX.vecHW2_of rightDiagonalActionFormula rightOffDiagonalActionFormula))
    (shapeOf_of_cauchy hC) (rankLe_of_cauchy hC)

end PI.FJM
end
end

