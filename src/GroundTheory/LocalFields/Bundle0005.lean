module

public import Mathlib
public import GroundTheory.LocalFields.Bundle0003
public import GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.GlobalFields.HerbrandQuotients.Bundle0001
public import GroundTheory.LocalFields.Eisenstein

@[expose] public section

-- bundled from GroundTheory.LocalFields.HerbrandLocalBase
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def unitsToTateZero : Kˣ →* TateZero (L ≃ₐ[K] L) Lˣ :=
  (QuotientGroup.mk' _).comp
    ((Units.map (algebraMap K L : K →* L)).codRestrict (invariants (L ≃ₐ[K] L) Lˣ) fun a g => by
      ext
      simp [AlgEquiv.smul_units_def])

theorem coe_tateNorm_units (x : Lˣ) :
    ((tateNorm (L ≃ₐ[K] L) Lˣ x : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L)) := by
  rw [algebraMap_norm_eq_prod, tateNorm_apply, Units.coe_prod]
  rfl

theorem unitsToTateZero_surjective : Function.Surjective (unitsToTateZero (K := K) (L := L)) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hfix : ∀ y : L, (∀ g : L ≃ₐ[K] L, g y = y) → ∃ a : K, algebraMap K L a = y := fun y hy =>
    (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy
  obtain ⟨a, ha⟩ := hfix (x : L) fun g => congrArg Units.val (hx g)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact x.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, congrArg (QuotientGroup.mk' _) (Subtype.ext (Units.ext ha))⟩

theorem ker_unitsToTateZero : (unitsToTateZero (K := K) (L := L)).ker = (normUnits K L).range := by
  ext a
  rw [MonoidHom.mem_ker, unitsToTateZero, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ((algebraMap K L).injective ?_)⟩
    rw [coe_normUnits, ← coe_tateNorm_units, hy]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨y, Units.ext ?_⟩
    rw [coe_tateNorm_units]
    rfl

theorem natCard_tateZero_units_eq :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Nat.card (Kˣ ⧸ (normUnits K L).range) := by
  rw [← ker_unitsToTateZero]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ unitsToTateZero_surjective).toEquiv.symm

end Galois

section Ord

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]


variable (L) in
def unitsOrd : Additive Lˣ →+ ℤ where
  toFun x := ord ((x.toMul : Lˣ) : L)
  map_zero' := by
    have := ord_unit (K := L) 1
    simpa using this
  map_add' x y := by
    change ord (((x.toMul * y.toMul : Lˣ)) : L) = _
    rw [Units.val_mul, ord_mul x.toMul.ne_zero y.toMul.ne_zero]

theorem unitsOrd_ofMul (x : Lˣ) : unitsOrd (L := L) (Additive.ofMul x) = ord (x : L) :=
  rfl

theorem unitsOrd_surjective : Function.Surjective (unitsOrd (L := L)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  intro n
  refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
  rw [map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]

theorem ord_eq_zero_iff_mem_range_unitsIncl (x : Lˣ) :
    ord (x : L) = 0 ↔ x ∈ (unitsIncl L).range := by
  rw [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]

theorem exact_unitsIncl_unitsOrd :
    Function.Exact (MonoidHom.toAdditive (unitsIncl L)) (unitsOrd (L := L)) := by
  intro y
  change ord ((y.toMul : Lˣ) : L) = 0 ↔ _
  rw [ord_eq_zero_iff_mem_range_unitsIncl]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.toMul, rfl⟩

end Ord

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem ord_algEquiv (σ : L ≃ₐ[K] L) (x : L) : ord (σ x) = ord x := by
  rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
    valuation_algEquiv_apply K L σ x]

theorem unitsOrd_smul (σ : L ≃ₐ[K] L) (x : Lˣ) :
    unitsOrd (L := L) (Additive.ofMul (σ • x)) = unitsOrd (L := L) (Additive.ofMul x) := by
  rw [unitsOrd_ofMul, unitsOrd_ofMul, AlgEquiv.smul_units_def, Units.coe_map]
  exact ord_algEquiv σ x

theorem unitsOrd_cycSubOne (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd (L := L) (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd (L := L) x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply,
    unitsOrd_smul, Representation.trivial_apply]
  rfl

theorem unitsOrd_cycNorm (x : Additive Lˣ) :
    unitsOrd (L := L) (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) x) =
      cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) (unitsOrd (L := L) x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycNorm_apply, cycNorm_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]
  rfl

variable {σ : L ≃ₐ[K] L}

theorem cycHerbrand_units_eq_mul (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hA : HasHerbrandQuotient
      (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
      (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ))) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ *
          Fintype.card (L ≃ₐ[K] L) := by
  have hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L)) := unitsIncl_injective
  have hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) :=
    hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ
  have hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L) :=
    cyclicHerbrand_trivial_int σ
  refine ⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩
  rw [cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]
  rfl

theorem cycHerbrand_integerUnits_eq_one_of_subgroup (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  have : V.subtype.range.FiniteIndex := by rw [Subgroup.range_subtype]; infer_instance
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ
  obtain ⟨h3, h4⟩ := cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ
  exact ⟨h1.mp h3, h2.symm.trans h4⟩

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.Monogenic
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem residue_aeval_integer (p : 𝒪[K][X]) (x : 𝒪[L]) :
    residue 𝒪[L] (aeval x p) = aeval (residue 𝒪[L] x) (p.map (residue 𝒪[K])) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1


variable (K) in
theorem adjoin_eq_top_of_residue_of_addVal_eq_one {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} = ⊤) {π : 𝒪[L]}
    (hπA : π ∈ Algebra.adjoin 𝒪[K] {x}) (hπ : addVal 𝒪[L] π = 1) :
    Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  set A := Algebra.adjoin 𝒪[K] {x}
  set e := (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K)))

  have hres : ∀ w : 𝒪[L], ∃ a ∈ A, ∃ w', w = a + π * w' := by
    intro w
    have hw : residue 𝒪[L] w ∈ Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} := by
      rw [hx]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
    obtain ⟨p, hp⟩ := hw
    obtain ⟨p₀, rfl⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective p
    refine ⟨aeval x p₀, ?_, ?_⟩
    · exact aeval_mem_adjoin_singleton 𝒪[K] x
    have hm : w - aeval x p₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
      rw [← residue_eq_zero_iff, map_sub, residue_aeval_integer]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
      rw [hp, sub_self]
    rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[L]), mem_maximalIdeal_pow_iff_le_addVal, Nat.cast_one, ← hπ,
      addVal_le_iff_dvd] at hm
    obtain ⟨w', hw'⟩ := hm
    exact ⟨w', by rw [← hw']; ring⟩
  have step : ∀ k : ℕ, ∀ z : 𝒪[L], ∃ a ∈ A, ∃ w, z = a + π ^ k * w := by
    intro k
    induction k with
    | zero => exact fun z => ⟨0, zero_mem _, z, by simp⟩
    | succ k ih =>
      intro z
      obtain ⟨a, ha, w, rfl⟩ := ih z
      obtain ⟨b, hb, w', rfl⟩ := hres w
      refine ⟨a + π ^ k * b, add_mem ha (mul_mem (pow_mem hπA k) hb), w', ?_⟩
      ring
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  have hassoc : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (π ^ e) := by
    rw [← addVal_eq_iff_associated, addVal_algebraMap_integer, addVal_uniformizer hϖK,
      addVal_pow, hπ, mul_one, nsmul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := hassoc
  have hle : (⊤ : Submodule 𝒪[K] 𝒪[L]) ≤
      Subalgebra.toSubmodule A ⊔ IsLocalRing.maximalIdeal 𝒪[K] • ⊤ := by
    intro z _
    obtain ⟨a, ha, w, rfl⟩ := step e z
    refine Submodule.add_mem_sup ha ?_
    rw [← hu, mul_assoc, ← Algebra.smul_def]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [hϖK.maximalIdeal_eq]
    exact Ideal.subset_span rfl
  have hnak := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  rw [eq_top_iff]
  intro z _
  exact hnak Submodule.mem_top


variable (K L) in
theorem exists_integer_adjoin_eq_top : ∃ x : 𝒪[L], Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  classical
  obtain ⟨ξ, hξ⟩ := Field.exists_primitive_element_of_finite_top 𝓀[K] 𝓀[L]
  have hadj : Algebra.adjoin 𝓀[K] {ξ} = ⊤ := IntermediateField.adjoin_eq_top_iff.mp hξ
  have hint : IsIntegral 𝓀[K] ξ := Algebra.IsIntegral.isIntegral ξ
  set P := minpoly 𝓀[K] ξ
  have hsep : P.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  obtain ⟨P₀, hP₀⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective P
  obtain ⟨x₀, hx₀⟩ := residue_surjective ξ

  have hy₀ : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    rw [← residue_eq_zero_iff, residue_aeval_integer, hP₀, hx₀]
    exact minpoly.aeval _ _
  have hd₀ : IsUnit (aeval x₀ (derivative P₀)) := by
    rw [← not_not (a := IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff,
      residue_aeval_integer, ← derivative_map, hP₀, hx₀]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)

  obtain ⟨x, hxres, hxval⟩ : ∃ x : 𝒪[L], residue 𝒪[L] x = ξ ∧ addVal 𝒪[L] (aeval x P₀) = 1 := by
    by_cases hsq : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
      have hϖ1 : addVal 𝒪[L] ϖ = 1 := addVal_uniformizer hϖ
      refine ⟨x₀ + ϖ, ?_, ?_⟩
      · rw [map_add (f := _), hx₀, (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, add_zero]
      obtain ⟨k, hk⟩ := binomExpansion (P₀.map (algebraMap 𝒪[K] 𝒪[L])) x₀ ϖ
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hϖm : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] := hϖ.not_isUnit
      have hϖsq : ϖ ^ 2 ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := Ideal.pow_mem_pow hϖm 2
      refine addVal_eq_one_of_mem_of_notMem_sq ?_ ?_
      · rw [hk]
        refine add_mem (add_mem hy₀ (Ideal.mul_mem_left _ _ hϖm)) ?_
        exact Ideal.mul_mem_left _ _ (Ideal.pow_le_self two_ne_zero hϖsq)
      · intro hmem
        have h1 : aeval x₀ (derivative P₀) * ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have : aeval x₀ (derivative P₀) * ϖ =
              aeval (x₀ + ϖ) P₀ - aeval x₀ P₀ - k * ϖ ^ 2 := by rw [hk]; ring
          rw [this]
          exact sub_mem (sub_mem hmem hsq) (Ideal.mul_mem_left _ _ hϖsq)
        obtain ⟨v, hv⟩ := hd₀
        have h2 : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have := Ideal.mul_mem_left (IsLocalRing.maximalIdeal 𝒪[L] ^ 2) (↑v⁻¹ : 𝒪[L]) h1
          rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at this
        rw [mem_maximalIdeal_pow_iff_le_addVal, hϖ1] at h2
        norm_num at h2
    · exact ⟨x₀, hx₀, addVal_eq_one_of_mem_of_notMem_sq hy₀ hsq⟩
  refine ⟨x, adjoin_eq_top_of_residue_of_addVal_eq_one K (π := aeval x P₀) ?_ ?_ hxval⟩
  · rw [hxres]; exact hadj
  · exact aeval_mem_adjoin_singleton 𝒪[K] x

end GroundTheory.LocalField
end
end

