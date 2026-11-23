module

public import Mathlib
public import GroundTheory.LocalFields.Different
public import GroundTheory.LocalFields.Bundle0012
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0068
public import GroundTheory.LocalFields.LocalFourier
public import GroundTheory.LocalFields.LubinTateTower

@[expose] public section

-- bundled from GroundTheory.LocalFields.DifferentGalois
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]


variable {K L} in
theorem map_minpoly_eq_prod {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (minpoly 𝒪[K] x).map (algebraMap 𝒪[K] 𝒪[L]) =
      ∏ σ : L ≃ₐ[K] L, (X - C (integerAlgEquiv K L σ x)) :=
  _root_.UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod hx


variable {K L} in
theorem aeval_derivative_minpoly_eq_prod [DecidableEq (L ≃ₐ[K] L)] {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    aeval x (derivative (minpoly 𝒪[K] x)) =
      ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - integerAlgEquiv K L σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, map_minpoly_eq_prod hx, derivative_prod_finset,
    eval_finsetSum, Finset.sum_eq_single (1 : L ≃ₐ[K] L)]
  · rw [eval_mul, derivative_X_sub_C, eval_one, mul_one, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  · intro σ _ hσ
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := 1) ?_ ?_) _
    · exact Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ _⟩
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem differentExponent_eq_sum_lowerIndex [DecidableEq (L ≃ₐ[K] L)] :
    (differentExponent K L : ℕ∞) =
      ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ := by
  obtain ⟨x, hx⟩ := exists_integer_adjoin_eq_top (K := K) (L := L)
  rw [differentExponent_eq_addVal hx, aeval_derivative_minpoly_eq_prod hx, addVal_prod]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_eq_top hx, ← AddValuation.map_neg, neg_sub]

theorem differentExponent_eq_sum_card_lowerRamificationGroup {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    differentExponent K L =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
  classical
  have h := differentExponent_eq_sum_lowerIndex K L
  have hσ : ∀ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), lowerIndex K L σ =
      (((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card : ℕ∞) := by
    intro σ hσ
    have hne : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hne)
    have hnN : n ≤ N := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have hmem : σ ∈ lowerRamificationGroup K L N := by
        rw [mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]
        exact_mod_cast hlt
      rw [hN, Subgroup.mem_bot] at hmem
      exact hne hmem
    have hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) =
        Finset.range n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]
      omega
    rw [← hn, hfilter, Finset.card_range]
  rw [Finset.sum_congr rfl hσ] at h
  have hswap : ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L),
      ((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card =
      ∑ i ∈ Finset.range N, (Nat.card (lowerRamificationGroup K L i) - 1) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.card_filter, Finset.filter_erase, Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem _⟩), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
  rw [← hswap]
  exact_mod_cast h

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LocalFourierExistence
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

section RatCircle

def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))

theorem ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this)

def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal

theorem ratCircleChar_injective : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective

theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _

end RatCircle

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Existence

theorem exists_mem_valBall_neg_one_notMem_valBall_zero :
    ∃ x : K, x ∈ valBall K (-1) ∧ x ∉ valBall K 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hi : (ϖ : K)⁻¹ ≠ 0 := inv_ne_zero h0
  refine ⟨(ϖ : K)⁻¹, ?_, ?_⟩
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
    omega

theorem continuous_of_isTrivialOn {χ : AddChar K Circle} {n : ℤ} (h : IsTrivialOn χ n) :
    Continuous χ := by
  have hlc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{z | z - x ∈ valBall K n},
      (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
    have e : x + (z - x) = z := by abel
    rw [← e, AddChar.map_add_eq_mul, h _ hz, mul_one]
  exact hlc.continuous

theorem exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by
  obtain ⟨x, hx1, hx0⟩ := exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)
  let π : K →+ K ⧸ valBall K 0 := QuotientAddGroup.mk' (valBall K 0)
  have hπx : π x ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx
  let ψ : AddChar K Circle :=
    ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)
  have hψ : ∀ y, ψ y = ratCircleChar (c (π y)) := fun _ => rfl
  refine ⟨ψ, fun y hy => ?_, fun h => ?_⟩
  · have : π y = 0 := by
      rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [hψ, this, map_zero, AddChar.map_zero_eq_one]
  · exact hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))

theorem exists_addChar_addCharConductor_eq_zero :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0 := by
  obtain ⟨ψ, h0, h1⟩ := exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)
  have hc : Continuous ψ := continuous_of_isTrivialOn h0
  have hne : ψ ≠ 1 := by
    rintro rfl
    exact h1 fun _ _ => AddChar.one_apply _
  refine ⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩
  by_contra hlt
  exact h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

theorem exists_addChar_continuous_ne_one :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩

end Existence

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.LubinTatePrimitive
section
noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel Polynomial Topology

namespace FormalGroup

section Associated

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem associated_psEval {φ : PowerSeries 𝒪[K]} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : IsUnit (PowerSeries.coeff 1 φ)) (a : 𝒪[L]) (ha : a ∈ 𝓂[L]) :
    Associated a ⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ := by
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφc : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  have hev := hasEval_of_mem_maximalIdeal (a := fun _ : Unit => a) fun _ => ha
  set ε := MvPowerSeries.eval₂Hom hφc hev
  have hval : (⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ : 𝒪[L])
      = ε φ := by
    apply Subtype.ext
    rw [MvPowerSeries.coe_eval₂Hom]
    exact psEval_eq_eval₂ φ (fun _ => a) fun _ => ha
  have hεX : ε PowerSeries.X = a := by
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_X _ _ _
  have hεC : ∀ c : 𝒪[K], ε (PowerSeries.C c) = algebraMap 𝒪[K] 𝒪[L] c := by
    intro c
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_C _ _ _
  obtain ⟨ψ, hψ⟩ := PowerSeries.X_dvd_iff.mpr h0
  set c := PowerSeries.constantCoeff ψ
  have hc : c = PowerSeries.coeff 1 φ := by
    rw [hψ, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨χ, hχ⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (ψ - PowerSeries.C c) = 0 by simp [c])
  have hψ' : ψ = PowerSeries.C c + PowerSeries.X * χ := by
    rw [← hχ]
    ring
  have hunit : IsUnit (ε ψ) := by
    rw [hψ', map_add (f := _), map_mul, hεX, hεC]
    by_contra hnu
    have hm : algebraMap 𝒪[K] 𝒪[L] c + a * ε χ ∈ 𝓂[L] := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hm' : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right (ε χ) _ ha)
      rwa [add_sub_cancel_right] at this
    rw [hc] at hm'
    exact (IsLocalRing.mem_maximalIdeal _).mp hm' (h1.map _)
  rw [hval, hψ, map_mul, hεX]
  exact ⟨hunit.unit, rfl⟩

end Associated

section Torsion

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

theorem lubinTateTorsion_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateTorsion Ω (hπ := hπ) hf m ≤ lubinTateTorsion Ω (hπ := hπ) hf n :=
  Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π h)

theorem lubinTateField_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateField Ω hπ hf m ≤ lubinTateField Ω hπ hf n := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact val_mem_lubinTateField hπ hf (lubinTateTorsion_mono hπ hf h hx)

theorem aeval_ltEisenstein_of_primitive {k : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (k + 1))
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) k) :
    aeval l.val ((ltEisenstein π k).map (algebraMap 𝒪[K] K)) = 0 :=
  aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl)
    fun h => hl' ((mem_lubinTateTorsion_ltPoly_iff k l).mpr h)


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem exists_integer_eq {E : IntermediateField K Ω} {x : Ω} (hxE : x ∈ E)
    (hx : valuation Ω x < 1) : ∃ y : 𝒪[E], ((y : E) : Ω) = x :=
  ⟨⟨⟨x, hxE⟩, ((valuation_coe_lt_one_iff E ⟨x, hxE⟩).mp hx).le⟩, rfl⟩


theorem irreducible_of_eq_adjoin_of_isEisensteinAt {E : IntermediateField K Ω} [FiniteDimensional K E]
    {a : Ω} (hE : E = K⟮a⟯) {p : 𝒪[K][X]} (hp : p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < p.natDegree) (ha : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) {x : 𝒪[E]}
    (hx : ((x : E) : Ω) = a) : Irreducible x := by
  have haE : a ∈ E := hx ▸ (x : E).2
  set α : E := ⟨a, haE⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α p = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α p
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a p = 0
    rwa [← aeval_map_algebraMap K]
  have := irreducible_of_isEisensteinAt_root hp hn hα hgen
  convert this
  exact Subtype.ext hx

variable [IsSepClosed Ω]

theorem val_mem_lubinTateField_of_mem (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    {n : ℕ} {x : IdealPoint Ω (lubinTateFormalGroup hπ hg)} (hx : x ∈ lubinTateTorsion Ω hg n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  lubinTateField_eq (Ω := Ω) hπ hg hf n ▸ val_mem_lubinTateField hπ hg hx

theorem primitive_spec (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m := by
  obtain ⟨l₀, -, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, rfl⟩ := hgen l hl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  have hb : IsUnit b := by
    by_contra hb
    apply hl'
    have hmem := (IsLocalRing.mem_maximalIdeal b).mpr hb
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, smul_smul, (hann _).mpr]
    exact Ideal.mem_span_singleton.mpr ⟨c, by ring⟩
  obtain ⟨u, rfl⟩ := hb
  refine ⟨fun a => ?_, fun m hm => ?_⟩
  · rw [smul_smul, hann]
    exact Ideal.mul_unit_mem_iff_mem _ u.isUnit
  · obtain ⟨a, rfl⟩ := hgen m hm
    exact ⟨a * ↑u⁻¹, by rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]⟩

theorem exists_primitive (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n, l ∉ lubinTateTorsion Ω (hπ := hπ) hf (n - 1) := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, fun h => ?_⟩
  rw [mem_lubinTateTorsion, hann, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h
  omega

theorem lubinTateField_eq_adjoin_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hl hl'
  refine le_antisymm ?_ ?_
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact val_mem_lubinTateField hπ hf hl

theorem irreducible_of_primitive_ltPoly (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π k).natDegree := by
    rw [(ltEisenstein_monic π k).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) k)
  exact irreducible_of_eq_adjoin_of_isEisensteinAt hE (isEisensteinAt_ltEisenstein hπ k) hdeg
    (aeval_ltEisenstein_of_primitive hπ hl hl') hx

theorem irreducible_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  have hg₀ : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := isLubinTateSeries_ltPoly π
  obtain ⟨m, rfl⟩ := (lubinTatePointEquiv hf hg₀).surjective l
  replace hl := (lubinTatePointEquiv_mem_torsion_iff hf hg₀ n m).mp hl
  replace hl' := fun h => hl' ((lubinTatePointEquiv_mem_torsion_iff hf hg₀ (n - 1) m).mpr h)
  have hmE : m.val ∈ lubinTateField Ω hπ hf n := val_mem_lubinTateField_of_mem hπ hf hg₀ hl
  obtain ⟨y, hy⟩ := exists_integer_eq hmE m.valuation_lt_one
  have hyirr : Irreducible y := irreducible_of_primitive_ltPoly hπ hf hl hl' hy
  have hym : y ∈ 𝓂[lubinTateField Ω hπ hf n] := hyirr.not_isUnit
  set φ := (lubinTateHom hπ hf hg₀ 1).toPowerSeries
  have hassoc := associated_psEval (K := K) (L := lubinTateField Ω hπ hf n) (φ := φ)
    (lubinTateHom hπ hf hg₀ 1).constantCoeff_eq_zero'
    (by rw [coeff_one_lubinTateHom]; exact isUnit_one) y hym
  have hxe : x = ⟨_, psEval_mem_integer φ (fun _ => y) fun _ => hym⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, lubinTatePointEquiv_val]
    change psEval φ (fun _ => m.val) =
      ((psEval φ (fun _ => (y : lubinTateField Ω hπ hf n)) : lubinTateField Ω hπ hf n) : Ω)
    rw [← psEval_coe _ φ (fun _ => (y : lubinTateField Ω hπ hf n)) (fun _ => by rw [hy]; exact m.valuation_lt_one), hy]
  rw [hxe]
  exact hassoc.irreducible hyirr

end Torsion

end FormalGroup

end GroundTheory.LocalField
end
end

