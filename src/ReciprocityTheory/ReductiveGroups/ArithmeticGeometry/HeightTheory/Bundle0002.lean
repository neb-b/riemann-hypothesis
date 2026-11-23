module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hartogs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

theorem ufd_mem_of_forall_prime {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x : FractionRing R)
    (h : ∀ p : R, Prime p → ∃ a b : R, ¬ p ∣ b ∧ x * algebraMap R (FractionRing R) b =
      algebraMap R (FractionRing R) a) :
    ∃ a : R, x = algebraMap R (FractionRing R) a := by
  classical
  have key : ∀ c : R, c ≠ 0 → ∀ a0 : R, x * algebraMap R (FractionRing R) c =
      algebraMap R (FractionRing R) a0 → ∃ a : R, x = algebraMap R (FractionRing R) a := by
    intro c
    induction c using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h0; exact absurd rfl h0
    | h₂ u hu =>
      intro _ a0 hx
      refine ⟨a0 * ↑(hu.unit⁻¹), ?_⟩
      have hu' : algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹) = 1 := by
        rw [← map_mul]; simp
      calc x = x * (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹)) := by
              rw [hu', mul_one]
        _ = algebraMap R (FractionRing R) (a0 * ↑(hu.unit⁻¹)) := by rw [← mul_assoc, hx, map_mul]
    | h₃ c p hc hp ih =>
      intro _ a0 hx
      obtain ⟨a, b, hpb, hab⟩ := h p hp
      have hinj := IsFractionRing.injective R (FractionRing R)
      have e1 : a * (p * c) = a0 * b := by
        apply hinj
        simp only [map_mul] at hx hab ⊢
        linear_combination (-(algebraMap R (FractionRing R) p * algebraMap R (FractionRing R) c)) * hab +
          algebraMap R (FractionRing R) b * hx
      have hpa0 : p ∣ a0 := by
        have : p ∣ a0 * b := ⟨a * c, by rw [← e1]; ring⟩
        rcases hp.dvd_or_dvd this with h1 | h1
        · exact h1
        · exact absurd h1 hpb
      obtain ⟨a1, rfl⟩ := hpa0
      have hp0 : algebraMap R (FractionRing R) p ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
        exact fun h' => hp.ne_zero (hinj h')
      refine ih hc a1 ?_
      apply mul_left_cancel₀ hp0
      simp only [map_mul] at hx ⊢
      linear_combination hx
  obtain ⟨a0, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine key c hc0 a0 ?_
  rw [div_mul_cancel₀]
  rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
  exact fun h' => hc0 (IsFractionRing.injective R (FractionRing R) h')

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
section
namespace ReciprocityTheory.ChartRestriction.G.T0


set_option maxHeartbeats 1000000 in
theorem heights_arith
    (D δ L lr lw1 hN sF laW nuS c g0 i DF PP0' PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw G Pet
      aL ade aG1 aF aG2 HMM HL Hde HF SI SN Ssum δlogδ : ℝ)
    (hD : 3 ≤ D) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcg : c * g0 ≤ 1 / 2)
    (hg0 : 0 ≤ g0) (hi : 1 ≤ i)
    (hP : 1 ≤ PP0' ∧ 1 ≤ PN ∧ 1 ≤ tableLineDegreeFive ∧ 1 ≤ tableLineDegreeTwo ∧ 1 ≤ PI4 ∧ 1 ≤ Prw ∧ 1 ≤ G ∧ 1 ≤ Pet)
    (hlr0 : 0 ≤ lr) (hlr : lr ≤ Prw * L) (hlw1 : lw1 ≤ Prw * L) (hhN : hN / 2 ≤ Prw * L)
    (hDF : DF ≤ L) (hlaW : laW ≤ G * L) (hnu : nuS ≤ PN * L)

    (hUP : sF ≤ (D + 2) * δ * (PP0' * L + max 0 laW + lw1))
    (hb1 : HMM = sF + δ * hN / 2)

    (haL : aL ≤ 4 / 3 * δ) (hade0 : 0 ≤ ade) (hade : ade ≤ aL) (haG10 : 0 ≤ aG1) (haG1 : aG1 ≤ aL)
    (haF0 : 0 ≤ aF) (haF : aF ≤ (D + 4) * aL) (haG20 : 0 ≤ aG2) (haG2 : aG2 ≤ (D + 4) * aL)

    (h7a : HL ≤ HMM + δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * c * g0 * ade * lr + c * g0 * Hde)
    (h7b : Hde ≤ HL + (δ * PI4 * D * L + D * aG1 * lr))
    (h7c : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * lr)

    (hdi : 2 * SI ≤ δlogδ + 2 * Ssum + 2 * D * aF * lr + 2 * HF)
    (hdn : SN / i ≤ g0 * (Hde + D * ade * lr) + δ * Pet) :
    2 * SI ≤ δlogδ + 2 * Ssum + 8 / 3 * D * (D + 4) * δ * Prw * L +
        2 * (D + 4) * (D + 1) * δ *
          (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L ∧
      SN / i ≤ g0 * ((D + 1) * δ *
        (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L) + δ * Pet := by
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8⟩ := hP
  have hD0 : 0 ≤ D := by linarith
  have hD4 : 0 ≤ D + 4 := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ δ * L := mul_nonneg hδ hL0
  have hcg0 : 0 ≤ c * g0 := mul_nonneg hc0 hg0
  have haL' : ade ≤ 4 / 3 * δ := hade.trans haL
  have hPL : 0 ≤ Prw * L := mul_nonneg (by linarith) hL0
  have hδPL : 0 ≤ 4 / 3 * δ * (Prw * L) := mul_nonneg (by linarith) hPL
  have hmax : max 0 laW ≤ G * L := max_le (mul_nonneg (by linarith) hL0) hlaW
  have hin : PP0' * L + max 0 laW + lw1 ≤ (PP0' + G + Prw) * L := by linarith
  have hsF : sF ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
    hUP.trans (mul_le_mul_of_nonneg_left hin (mul_nonneg (by linarith) hδ))
  have hN2 : δ * hN / 2 ≤ δ * (Prw * L) := by
    have := mul_le_mul_of_nonneg_left hhN hδ
    linarith
  have hnu2 : δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := by
    apply mul_le_mul_of_nonneg_left _ hδ
    have h1 : tableLineDegreeFive * DF ≤ tableLineDegreeFive * L := mul_le_mul_of_nonneg_left hDF (by linarith)
    have h2 : c * tableLineDegreeTwo ≤ 1 * tableLineDegreeTwo := mul_le_mul_of_nonneg_right hc1 (by linarith)
    have h3 : tableLineDegreeTwo * 1 ≤ tableLineDegreeTwo * L := mul_le_mul_of_nonneg_left hL (by linarith)
    linarith
  have hcross : D * c * g0 * ade * lr ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have h1 : ade * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul haL' hlr hlr0 (by linarith)
    have h2 : c * g0 * (ade * lr) ≤ 1 / 2 * (4 / 3 * δ * (Prw * L)) :=
      mul_le_mul hcg h1 (mul_nonneg hade0 hlr0) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left h2 hD0
    linarith
  have hadl : D * ade * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h1 : ade * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul haL' hlr hlr0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hY1 : D * aG1 * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h1 : aG1 * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul (haG1.trans haL) hlr hlr0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hA4 : (D + 4) * aL ≤ (D + 4) * (4 / 3 * δ) := mul_le_mul_of_nonneg_left haL hD4
  have hY2 : D * aG2 * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h1 : aG2 * lr ≤ (D + 4) * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul (haG2.trans hA4) hlr hlr0 (mul_nonneg hD4 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hYF : D * aF * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h1 : aF * lr ≤ (D + 4) * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul (haF.trans hA4) hlr hlr0 (mul_nonneg hD4 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hPI : 0 ≤ δ * PI4 * D * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hδ (by linarith)) hD0) hL0
  have hXb0 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have e1 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
      mul_nonneg (mul_nonneg (by linarith) hδ) (mul_nonneg (by linarith) hL0)
    have e2 : 0 ≤ δ * (Prw * L) := mul_nonneg hδ hPL
    have e3 : 0 ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := mul_nonneg hδ (mul_nonneg (by linarith) hL0)
    have e4 : 0 ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := mul_nonneg hD0 (by linarith)
    linarith
  have hYb0 : 0 ≤ δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)) := by
    have := mul_nonneg hD0 hδPL
    linarith
  have hHde : Hde ≤ HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by linarith
  have hHL1 : HL ≤ ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      c * g0 * (HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)))) := by
    have := mul_le_mul_of_nonneg_left hHde hcg0
    linarith
  have hHL : HL ≤ 2 * ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by
    by_cases hHL0 : 0 ≤ HL
    · have a1 := mul_le_mul_of_nonneg_right hcg hHL0
      have a2 := mul_le_mul_of_nonneg_right hcg hYb0
      linarith
    · push_neg at hHL0
      linarith
  have hHF := mul_le_mul_of_nonneg_left hHL hD4
  have e1 : 0 ≤ (D + 4) * (6 * D + 4) * G := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e2 : 0 ≤ (D + 4) * (10 * D + 8) * PP0' := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e3 : 0 ≤ (D + 4) * (6 * D + 6) * Prw := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e4 : 0 ≤ (D + 4) * (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) :=
    mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e5 : 0 ≤ (11 * D * D + 55 * D + 48) * PI4 := mul_nonneg (by nlinarith) (by linarith)
  have hE := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg e1 e2) e3) e4) e5)
  have f1 : 0 ≤ (6 * D + 4) * G := mul_nonneg (by linarith) (by linarith)
  have f2 : 0 ≤ (10 * D + 8) * PP0' := mul_nonneg (by linarith) (by linarith)
  have f3 : 0 ≤ (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) := mul_nonneg (by linarith) (by linarith)
  have f4 : 0 ≤ (10 * D + 12) * PI4 := mul_nonneg (by linarith) (by linarith)
  have f5 : 0 ≤ (6 * D + 6) * Prw := mul_nonneg (by linarith) (by linarith)
  have hE2 := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg f1 f2) f3) f4) f5)
  constructor
  · linarith
  · have hb : Hde + D * ade * lr ≤ (D + 1) * δ * (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L := by linarith
    have := mul_le_mul_of_nonneg_left hb hg0
    linarith

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LinearIndependentC
section
namespace ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

lemma coeff_smul_C (q : MvPolynomial σ L) (e : E) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (q • C e : MvPolynomial σ E) m = algebraMap L E (AddMonoidAlgebra.coeff q m) * e := by
  rw [Algebra.smul_def, algebraMap_def, mul_comm, coeff_C_mul, coeff_map, mul_comm]

variable {n : Type} [Fintype n] (b : Module.Basis n L E)

noncomputable def crd (p : MvPolynomial σ E) (i : n) : MvPolynomial σ L :=
  ∑ m ∈ p.support, monomial m (b.repr (AddMonoidAlgebra.coeff p m) i)

lemma coeff_crd (p : MvPolynomial σ E) (i : n) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (crd b p i) m = b.repr (AddMonoidAlgebra.coeff p m) i := by
  classical
  rw [crd, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero, Finsupp.zero_apply]

lemma eq_sum_crd (p : MvPolynomial σ E) : p = ∑ i, crd b p i • (C (b i) : MvPolynomial σ E) := by
  ext m
  rw [coeff_sum]
  simp only [coeff_smul_C, coeff_crd, ← Algebra.smul_def]
  exact (b.sum_repr (AddMonoidAlgebra.coeff p m)).symm

lemma linearIndependent_C : LinearIndependent (MvPolynomial σ L) (fun i => (C (b i) : MvPolynomial σ E)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  apply MvPolynomial.ext
  intro m
  have h : ∑ j, AddMonoidAlgebra.coeff (g j) m • b j = 0 := by
    simpa only [coeff_sum, coeff_smul_C, ← Algebra.smul_def,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      congrArg (AddMonoidAlgebra.coeff · m) hg
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact (Fintype.linearIndependent_iff.1 b.linearIndependent) (fun j => AddMonoidAlgebra.coeff (g j) m) h i

end ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PTNonempty
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField Cardinal

private lemma countable_of_intermediateField_fg {K Ω : Type} [Field K] [Countable K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) : Countable Ω := by
  obtain ⟨S, hS⟩ := hfg
  haveI : Countable (MvPolynomial (S : Set Ω) K) := by
    first
    | infer_instance
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinal_mk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max_lift.trans
        (max_le (max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
          (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  let f : MvPolynomial (S : Set Ω) K × MvPolynomial (S : Set Ω) K → Ω := fun pq =>
    MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.1 /
      MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.2
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ IntermediateField.adjoin K (S : Set Ω) := by
      rw [hS]; exact IntermediateField.mem_top
    obtain ⟨r, hr, t, ht, rfl⟩ := (IntermediateField.mem_adjoin_iff_div).mp hx
    rw [Algebra.adjoin_eq_range] at hr ht
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := ht
    exact ⟨(p, q), rfl⟩
  exact hf.countable

theorem exists_embedding_over {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) (sg : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = sg := by
  haveI hKc : Countable K := by
    first
    | infer_instance
    | exact (Module.finBasis ℚ K).equivFun.injective.countable
  haveI hΩc : Countable Ω := countable_of_intermediateField_fg hfg
  letI : Algebra K ℂ := sg.toAlgebra
  haveI : FaithfulSMul K ℂ := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K ℂ).mpr sg.injective
  haveI : FaithfulSMul K Ω := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K Ω).mpr (algebraMap K Ω).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hKle : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have htt : Cardinal.aleph0 < Cardinal.mk t := by
    first
    | (by_contra hle
       have h := IsAlgClosed.cardinal_le_max_transcendence_basis _ ht
       exact absurd (h.trans (max_le (max_le hKle (not_lt.mp hle)) le_rfl)) (not_le.mpr hC))
    | (have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hKle hC
       rw [Cardinal.lift_inj] at h
       rw [h] at hC
       exact hC)
  have hst : Cardinal.mk s ≤ Cardinal.mk t := Cardinal.mk_le_aleph0.trans htt.le
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hst
  let u : s → ℂ := fun i => ((e i : t) : ℂ)
  have hu : AlgebraicIndependent K u := ht.1.comp e e.injective
  let E := hs.1.aevalEquiv.symm.trans hu.aevalEquiv
  let φ : Algebra.adjoin K (Set.range (Subtype.val : s → Ω)) →ₐ[K] ℂ :=
    (Algebra.adjoin K (Set.range u)).val.comp E.toAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp E.injective
  letI : Algebra (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    hs.isAlgebraic
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    NoZeroSMulDivisors.of_algebraMap_injective hφ
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ ℂ).mpr hφ
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    NoZeroSMulDivisors.of_algebraMap_injective Subtype.val_injective
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ Ω).mpr Subtype.val_injective
  let g : Ω →ₐ[Algebra.adjoin K (Set.range (Subtype.val : s → Ω))] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom, ?_⟩
  ext k
  have h1 : algebraMap K Ω k = algebraMap (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω
      (algebraMap K (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) k) := by
    first
    | rfl
    | exact IsScalarTower.algebraMap_apply _ _ _ k
  show g (algebraMap K Ω k) = sg k
  rw [h1, g.commutes]
  exact φ.commutes k

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw
section
namespace ReciprocityTheory.ChartRestriction.G.T0

def RegLaw {Λ Wt : Type*} (Forms : Wt → Type*) (Pt Pt' : Λ → Type*)
    (emb : ∀ la, Pt la → Pt' la) (v : ∀ la, Pt' la → ∀ {w : Wt}, Forms w → EReal)
    (Q : Type*) (ord : Q → ∀ {w : Wt}, Forms w → EReal)
    (NoZero : ∀ {w : Wt} {n : ℕ}, (Fin n → Forms w) → Prop) : Prop :=

  (∀ (w : Wt) (F : Forms w),
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) F) →
      (∀ la (y' : Pt' la), 0 ≤ v la y' F) ∧ ∀ q : Q, 0 ≤ ord q F) ∧

  (∀ (wL wE : Wt) (n : ℕ) (ws : Fin n → Forms wL) (et : Forms wE) (nu : Λ → ℝ) (c' : ℝ),
    0 ≤ c' → NoZero ws →
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) et ∧ (v la (emb la y) et ≠ ⊤ →
      (⨅ k, v la (emb la y) (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la (emb la y) et)) →
    (∀ la (y' : Pt' la), 0 ≤ v la y' et ∧ (v la y' et ≠ ⊤ →
      (⨅ k, v la y' (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la y' et)) ∧
    ∀ q : Q, 0 ≤ ord q et ∧ (ord q et ≠ ⊤ → (⨅ k, ord q (ws k)) ≤ (c' : EReal) * ord q et))

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SpanTopOfComplete
section
namespace ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete

theorem span_eq_top_of_complete {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N] (ϖ : O)
    [IsPrecomplete (Ideal.span {ϖ}) O]
    (hsep : ∀ x : N, (∀ k : ℕ, ∃ y : N, x = ϖ ^ k • y) → x = 0) {n : ℕ} (S : Fin n → N)
    (hS : ∀ x : N, ∃ c : Fin n → O, ∃ y : N, x = ∑ i, c i • S i + ϖ • y) :
    Submodule.span O (Set.range S) = ⊤ := by
  classical
  choose c y hcy using hS
  rw [eq_top_iff]
  intro x _
  let xs : ℕ → N := fun k => Nat.rec x (fun _ z => y z) k
  have hxs : ∀ k, xs (k + 1) = y (xs k) := fun k => rfl
  let a : ℕ → Fin n → O := fun k i => ∑ j ∈ Finset.range k, ϖ ^ j * c (xs j) i
  have hxa : ∀ k, x = ∑ i, a k i • S i + ϖ ^ k • xs k := by
    intro k
    induction k with
    | zero => simp [a, xs]
    | succ k ih =>
      have hk := hcy (xs k)
      calc x = ∑ i, a k i • S i + ϖ ^ k • xs k := ih
        _ = ∑ i, a k i • S i + ϖ ^ k • (∑ i, c (xs k) i • S i + ϖ • y (xs k)) := by rw [← hk]
        _ = ∑ i, a (k + 1) i • S i + ϖ ^ (k + 1) • xs (k + 1) := by
          rw [hxs]
          simp only [a, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
            smul_smul, pow_succ]
          abel

  have hmem : ∀ m k, m ≤ k → ∀ i, a k i - a m i ∈ Ideal.span {ϖ ^ m} := by
    intro m k hmk i
    have : a k i - a m i = ∑ j ∈ Finset.Ico m k, ϖ ^ j * c (xs j) i := by
      simp only [a]
      rw [← Finset.sum_range_add_sum_Ico _ hmk]
      ring
    rw [this]
    refine Ideal.sum_mem _ fun j hj => ?_
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow ϖ (Finset.mem_Ico.1 hj).1) _
  have hpow : ∀ m : ℕ, (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ i, ∃ L : O, ∀ k, a k i - L ∈ Ideal.span {ϖ ^ k} := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun k => a k i) (fun {m k} hmk => by
      rw [SModEq.sub_mem, hpow]
      have := hmem m k hmk i
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
    exact ⟨L, fun k => by have := hL k; rwa [SModEq.sub_mem, hpow] at this⟩
  choose L hL using hlim
  have hx : x = ∑ i, L i • S i := by
    rw [← sub_eq_zero]
    refine hsep _ fun k => ?_
    have ht : ∀ i, ∃ t : O, a k i - L i = ϖ ^ k * t := fun i => Ideal.mem_span_singleton'.1 (hL i k) |>.imp
      fun t ht => by rw [← ht, mul_comm]
    choose t ht using ht
    refine ⟨∑ i, t i • S i + xs k, ?_⟩
    conv_lhs => rw [hxa k]
    have e : ∀ i, a k i • S i = L i • S i + ϖ ^ k • t i • S i := by
      intro i
      rw [smul_smul, ← ht i, sub_smul]
      abel
    simp only [e, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
    abel
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete
end

