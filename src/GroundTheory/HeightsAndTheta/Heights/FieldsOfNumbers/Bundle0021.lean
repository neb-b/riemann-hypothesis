module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0010
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace FunctionFieldFinite

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

def chartGens (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    Set (FractionRing (MRing ι F ⧸ P)) :=
  Set.range fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))


omit [Fintype K] [DecidableEq K] in
theorem range_chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartMap P u).range = Algebra.adjoin F (chartGens P u) :=
  aeval_range _

theorem homFracDegZero_eq (hD : MChartDehomog.Statement.{u}) (P : Ideal (MRing ι F)) [P.IsPrime]
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    homFracDegZero P = IntermediateField.adjoin F (chartGens P u) := by
  apply le_antisymm
  · unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, f, g, hf, hg, -, rfl⟩
    have hm : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
      rw [chartMonomial, map_prod, map_prod]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
      rw [map_pow, map_pow]
      refine pow_ne_zero _ ?_
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    have hr : ∀ p, chartMap P u p ∈ IntermediateField.adjoin F (chartGens P u) := fun p =>
      IntermediateField.algebra_adjoin_le_adjoin F _ (by rw [← range_chartMap]; exact ⟨p, rfl⟩)
    have key := div_mem (hr f) (hr g)
    rwa [hD F K ι P u hu f b hf, hD F K ι P u hu g b hg, div_div_div_cancel_right₀ hm] at key
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨blockWeight ι v, X v, X ⟨v.1, u v.1⟩,
      isWeightedHomogeneous_X _ _ _, isWeightedHomogeneous_X _ _ _, hu v.1, rfl⟩


open IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_homFracDegZero (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.trdeg F (homFracDegZero P) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P) := by
  haveI : Algebra.FiniteType F (Algebra.adjoin F (chartGens P u)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  rw [← hT F K ι P hP u hu, homFracDegZero_eq hD P u hu,
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F)
      (A := Algebra.adjoin F (chartGens P u)), ← range_chartMap]
  exact congrArg (· + _) (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq.symm

theorem relDim_eq_trdeg (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiProjPrime P) :
    ∃ n : ℕ, Algebra.trdeg F (homFracDegZero P) = n ∧
      relDim P = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  choose u hu using hP.relevant
  have h1 := trdeg_homFracDegZero hD hT P hP.multiHomog u hu
  obtain ⟨m, hdim, htr⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MRing ι F ⧸ P)
  rw [htr] at h1
  have hlt : Algebra.trdeg F (homFracDegZero P) < Cardinal.aleph0 :=
    lt_of_le_of_lt (h1 ▸ self_le_add_right _ _) (Cardinal.natCast_lt_aleph0 (n := m))
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hn] at h1
  have hnm : n + Fintype.card K = m := by exact_mod_cast h1
  refine ⟨n, hn, ?_⟩
  have hz : (((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) = n := by push_cast; ring
  rw [relDim, hdim, ← hnm, ← hz]
  rfl

end FunctionFieldFinite


open FunctionFieldFinite in
theorem FunctionFieldFinite.proof (hD : MChartDehomog.Statement.{u})
    (hT : MChartTrdeg.Statement.{u}) : FunctionFieldFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hrel
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  obtain ⟨n, hn, hrn⟩ := relDim_eq_trdeg hD hT (contractPrime j P') hP
  obtain ⟨n', hn', hrn'⟩ := relDim_eq_trdeg hD hT P' hP'
  have hnn : n = n' := by
    rw [hrel, hrn'] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  set E := (homFracDegZero (contractPrime j P')).map (contractFracMap j P')
  set κ' := homFracDegZero P'
  have h : E ≤ κ' := map_homFracDegZero_le j ι' P'
  have hE : Algebra.trdeg F E = n :=
    (IntermediateField.equivMap _ (contractFracMap j P')).trdeg_eq.symm.trans hn
  let _ : Algebra E κ' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E κ' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul E κ' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IntermediateField.inclusion h).injective
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  have htow := trdeg_add_eq F E (A := κ')
  rw [hE, hn', ← hnn] at htow
  have hlt : Algebra.trdeg E κ' < Cardinal.aleph0 :=
    lt_of_le_of_lt (htow ▸ self_le_add_left _ _) (Cardinal.natCast_lt_aleph0 (n := n))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at htow
  have hm0 : m = 0 := by
    have : n + m = n := by exact_mod_cast htow
    omega
  have : Algebra.IsAlgebraic E κ' := trdeg_eq_zero_iff.mp (by rw [hm, hm0]; rfl)
  let g : κ' →ₐ[E] FractionRing (MRing ι' F ⧸ P') :=
    { (κ'.val : κ' →+* FractionRing (MRing ι' F ⧸ P')) with commutes' := fun _ => rfl }
  choose u hu using hP'.relevant
  have hκ' : κ' = IntermediateField.adjoin F (chartGens P' u) := homFracDegZero_eq hD P' u hu
  have hint : ∀ x ∈ chartGens P' u, IsIntegral E x := by
    intro x hx
    have hx' : x ∈ κ' := hκ' ▸ IntermediateField.subset_adjoin F _ hx
    have hy : IsAlgebraic E (⟨x, hx'⟩ : κ') := Algebra.IsAlgebraic.isAlgebraic _
    exact IsIntegral.map g hy.isIntegral
  have : Finite (chartGens P' u) := (Set.finite_range _).to_subtype
  have := IntermediateField.finiteDimensional_adjoin hint
  show IntermediateField.relfinrank E κ' ≠ 0
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  have hext : IntermediateField.extendScalars h = IntermediateField.adjoin E (chartGens P' u) := by
    rw [← IntermediateField.extendScalars_adjoin (h.trans hκ'.le)]
    exact IntermediateField.ext fun x =>
      show x ∈ κ' ↔ x ∈ IntermediateField.adjoin F (chartGens P' u) by rw [hκ']
  rw [hext]
  exact Module.finrank_pos.ne'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem prod_pow_blockWeight {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1]
  · simp [blockWeight]
  · intro k _ hk
    simp [blockWeight, Pi.single_eq_of_ne hk]
  · simp

theorem MChartDehomog.proof : MChartDehomog.Statement := by
  intro F _ K _ _ ι P _ u hu f b hf
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  let w : K → L := fun k => φ (X ⟨k, u k⟩)
  have hw : ∀ k, w k ≠ 0 := fun k => by
    simp only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  have hD : φ (chartMonomial u b) = ∏ k, w k ^ b k := by
    simp [chartMonomial, w, map_prod, map_pow]
  have hC : ∀ c : F, φ (C c) = algebraMap F L c := fun c => by
    simp only [φ, RingHom.comp_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hmono : ∀ e ∈ f.support, chartMap P u (monomial e (AddMonoidAlgebra.coeff f e)) * ∏ k, w k ^ b k =
      φ (monomial e (AddMonoidAlgebra.coeff f e)) := by
    intro e he
    have hwe : Finsupp.weight (blockWeight ι) e = b := hf (mem_support_iff.mp he)
    rw [← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul,
      monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    change (φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)
    rw [← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]
  change chartMap P u f = φ f / φ (chartMonomial u b)
  rw [hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem chartMonomial_add (u : ∀ k, ι k) (a c : K → ℕ) :
    (chartMonomial u (a + c) : MRing ι F) = chartMonomial u a * chartMonomial u c := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (c : K → ℕ) :
    IsMultiHomog (chartMonomial u c : MRing ι F) c := by
  show IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, u k⟩ : MRing ι F) ^ c k) c
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, u k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (c k))
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]

theorem finsuppProd_chartVar (u : ∀ k, ι k) (e : (Σ k, ι k) →₀ ℕ) :
    (e.prod fun v n => (X ⟨v.1, u v.1⟩ : MRing ι F) ^ n) =
      chartMonomial u (Finsupp.weight (blockWeight ι) e) := by
  induction e using Finsupp.induction_linear with
  | zero => simp [chartMonomial]
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add (f := _),
      chartMonomial_add]
  | single v n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
    simp only [chartMonomial]
    rw [Finset.prod_eq_single v.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, hk]
    · simp

theorem chartMap_monomial_mul (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) (e : (Σ k, ι k) →₀ ℕ) (c : F) :
    chartMap P u (monomial e c) *
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
          (Ideal.Quotient.mk P (chartMonomial u (Finsupp.weight (blockWeight ι) e))) =
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (monomial e c)) := by
  have hy : ∀ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ≠ 0 := fun k => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  rw [← finsuppProd_chartVar, chartMap, aeval_monomial, monomial_eq]
  simp only [map_mul, map_finsuppProd, map_pow]
  rw [mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hy v.1))]

theorem MChartHomog.proof : MChartHomog.Statement.{u} := by
  intro F _ K _ _ ι u p
  classical
  obtain ⟨b, hle⟩ : ∃ b : K → ℕ, ∀ e ∈ p.support, Finsupp.weight (blockWeight ι) e ≤ b :=
    ⟨fun k => p.support.sup fun e => Finsupp.weight (blockWeight ι) e k, fun e he k =>
      Finset.le_sup (f := fun e => Finsupp.weight (blockWeight ι) e k) he⟩
  refine ⟨b, ∑ e ∈ p.support,
    monomial e (AddMonoidAlgebra.coeff p e) * chartMonomial u (b - Finsupp.weight (blockWeight ι) e), ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWeightedHomogeneous_monomial (blockWeight ι) e (AddMonoidAlgebra.coeff p e) rfl).mul
      (chartMonomial_isMultiHomog (F := F) u (b - Finsupp.weight (blockWeight ι) e))
    rwa [add_tsub_cancel_of_le (hle e he)] at this
  · intro P _ hu
    have hY : ∀ c, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u c)) ≠ 0 := fun c => by
      simp only [chartMonomial, map_prod, map_pow]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    rw [eq_div_iff (hY b)]
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have key : (chartMonomial u b : MRing ι F) = chartMonomial u (Finsupp.weight (blockWeight ι) e) *
        chartMonomial u (b - Finsupp.weight (blockWeight ι) e) := by
      rw [← chartMonomial_add, add_tsub_cancel_of_le (hle e he)]
    rw [key, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, chartMap_monomial_mul P u hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartLocDim

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k))
  unfold IsMultiHomog chartMonomial
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]


omit [DecidableEq K] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hu k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)


omit [Fintype K] [DecidableEq K] in
theorem algebraMap_mk_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {g : MRing ι F} (hg : g ∉ Q) :
    algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q)) (Ideal.Quotient.mk Q g) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact hg


omit [DecidableEq K] in
theorem mem_chartIdeal_iff (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) {p h : MRing ι F} {b : K → ℕ}
    (hp : chartMap Q u p = algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q))
      (Ideal.Quotient.mk Q h) / algebraMap (MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (chartMonomial u b))) :
    p ∈ chartIdeal Q u ↔ h ∈ Q := by
  rw [chartIdeal, RingHom.mem_ker, hp, div_eq_zero_iff,
    or_iff_left (algebraMap_mk_ne_zero Q (chartMonomial_not_mem Q u hu b)),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]


omit [Fintype K] in
theorem chartMap_mem (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (p : MRing ι F) : chartMap P u p ∈ degZeroLoc P {W} := by
  have hr : (chartMap P u).range ≤ degZeroLoc P {W} := by
    rw [chartMap, aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) v)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (fun h => hu v.1 (hPW h)) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hu v.1)
  exact hr ⟨p, rfl⟩

def toLoc (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) : (MRing ι F ⧸ chartIdeal P u) →+* degZeroLoc P {W} :=
  Ideal.Quotient.lift (chartIdeal P u)
    ((chartMap P u).toRingHom.codRestrict (degZeroLoc P {W}) (chartMap_mem P W hPW u hu))
    (fun _ ha => Subtype.ext (RingHom.mem_ker.mp ha))

end MChartLocDim


open MChartLocDim in
theorem MChartLocDim.proof (h₁ : DegZeroLocQuot.Statement.{u}) (h₂ : MChartDehomog.Statement.{u})
    (h₃ : MChartHomog.Statement.{u}) : MChartLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P W _ _ hPW u hu
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hQ⟩ := h₃ F K ι u p
    exact (mem_chartIdeal_iff W u hu (hQ W hu)).2 (hPW ((mem_chartIdeal_iff P u huP (hQ P huP)).1 hp))
  set q := (chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hle)
  let _ := (toLoc P W hPW u hu).toAlgebra
  have hmap : ∀ p, ((algebraMap (MRing ι F ⧸ chartIdeal P u) (degZeroLoc P {W})
      (Ideal.Quotient.mk _ p) : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = chartMap P u p :=
    fun p => rfl
  have hmemq : ∀ p, Ideal.Quotient.mk (chartIdeal P u) p ∈ q ↔ p ∈ chartIdeal W u :=
    fun p => Ideal.mem_quotient_iff_mem hle
  have : IsLocalization.AtPrime (degZeroLoc P {W}) q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hpW : p ∉ chartIdeal W u := fun h => ha ((hmemq p).2 h)
      obtain ⟨b, h, hh, hQ⟩ := h₃ F K ι u p
      have hhW : h ∉ W := fun h' => hpW ((mem_chartIdeal_iff W u hu (hQ W hu)).2 h')
      have hinv := div_mem_degZeroLoc P {W} (chartMonomial_isMultiHomog u b) hh (fun h' => hhW (hPW h'))
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hhW)
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      rw [Subalgebra.coe_mul, hmap, hQ P huP, Subalgebra.coe_one,
        div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b))
        (algebraMap_mk_ne_zero P (fun h' => hhW (hPW h')))
    · rintro ⟨x, hx⟩
      obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := h₁ F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; infer_instance) x hx
      have hgW' : g ∉ W := hgW W rfl
      have hgq : Ideal.Quotient.mk (chartIdeal P u) g ∈ q.primeCompl := fun h' =>
        hgW' ((mem_chartIdeal_iff W u hu (h₂ F K ι W u hu g b hg)).1 ((hmemq g).1 h'))
      refine ⟨(Ideal.Quotient.mk _ f, ⟨_, hgq⟩), Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hmap, hmap, h₂ F K ι P u huP g b hg, h₂ F K ι P u huP f b hf]
      have h1 := algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)
      have h2 := algebraMap_mk_ne_zero P hgP
      field_simp
    · intro a c hac
      refine ⟨1, ?_⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h := congrArg Subtype.val hac
      rw [hmap, hmap, ← sub_eq_zero, ← map_sub] at h
      rw [Submonoid.coe_one, one_mul, one_mul]
      exact Ideal.Quotient.eq.mpr (RingHom.mem_ker.mpr h)
  exact IsLocalization.AtPrime.ringKrullDim_eq_height q (degZeroLoc P {W})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

