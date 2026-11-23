module

public import Mathlib
public import GroundTheory.LocalFields.UnitsBasic
public import GroundTheory.LocalFields.Bundle0002
public import GroundTheory.TateCohomology.HerbrandAbstract
public import GroundTheory.GlobalFields.HerbrandQuotients.Bundle0001
public import GroundTheory.LocalFields.CompleteTrivial

@[expose] public section

-- bundled from GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
section
namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def unitFiltrationUnits (n : ℕ) : Subgroup Kˣ :=
  (unitFiltration K n).map (unitsIncl K)

variable {K}

theorem unitFiltrationUnits_antitone : Antitone (unitFiltrationUnits K) :=
  fun _ _ hmn ↦ Subgroup.map_mono (unitFiltration_antitone K hmn)

theorem mem_unitFiltrationUnits_zero_iff {x : Kˣ} :
    x ∈ unitFiltrationUnits K 0 ↔ valuation K (x : K) = 1 := by
  rw [unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map, mem_range_unitsIncl_iff,
    ← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]

theorem mem_unitFiltrationUnits_iff {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ valuation K ((x : K) - 1) ≤ valuation K (ϖ : K) ^ n := by
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := hu
    rw [hset] at this
    simpa using this
  · intro h
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hlt : valuation K ((x : K) - 1) < 1 :=
      h.trans_lt (pow_lt_one₀ zero_le hϖ1 (by omega))
    have hx1 : valuation K (x : K) = 1 := by
      have := (valuation K).map_one_add_of_lt hlt
      simpa using this
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr (by
      rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]; exact hx1)
    refine ⟨u, ?_, rfl⟩
    show ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    rw [hset]
    simpa using h

theorem isOpen_setOf_valuation_sub_le {a : K} {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    IsOpen {y : K | valuation K (y - a) ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z - a = (z - y) + (y - a) := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_le hz.le hy

theorem isOpen_setOf_valuation_lt {γ : ValueGroupWithZero K} :
    IsOpen {y : K | valuation K y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  have hγ : γ ≠ 0 := ne_bot_of_gt hy
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z = (z - y) + y := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_lt hz hy

theorem isOpen_setOf_valuation_eq_one : IsOpen {y : K | valuation K y = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun z hz ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_one] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation K).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem val_image_unitFiltrationUnits_zero :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K 0 : Set Kˣ) = {y : K | valuation K y = 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_unitFiltrationUnits_zero_iff.mp hx
  · intro hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y hy0, mem_unitFiltrationUnits_zero_iff.mpr hy, rfl⟩

theorem val_image_unitFiltrationUnits {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K n : Set Kˣ) =
      {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_unitFiltrationUnits_iff hn hϖ).mp hx
  · intro hy
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : valuation K ((0 : K) - 1) ≤ valuation K (ϖ : K) ^ n := hy
      simp only [zero_sub, Valuation.map_neg, map_one] at this
      exact (pow_lt_one₀ zero_le hϖ1 (by omega)).not_ge this
    exact ⟨Units.mk0 y hy0, (mem_unitFiltrationUnits_iff hn hϖ).mpr hy, rfl⟩

theorem valuation_uniformizer_ne_zero {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hϖ.ne_zero

theorem isOpen_unitFiltrationUnits (n : ℕ) : IsOpen (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (unitFiltrationUnits K 0 : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K y = 1} := by
      ext x; exact mem_unitFiltrationUnits_zero_iff
    rw [this]
    exact isOpen_setOf_valuation_eq_one.preimage Units.continuous_val
  · have : (unitFiltrationUnits K n : Set Kˣ) =
        (↑) ⁻¹' {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
      ext x; exact mem_unitFiltrationUnits_iff hn hϖ
    rw [this]
    exact (isOpen_setOf_valuation_sub_le
      (pow_ne_zero _ (valuation_uniformizer_ne_zero hϖ))).preimage Units.continuous_val

theorem isCompact_unitFiltrationUnits (n : ℕ) : IsCompact (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Units.isEmbedding_val₀.isCompact_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [val_image_unitFiltrationUnits_zero]
    have : {y : K | valuation K y = 1} =
        {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
      constructor
      · intro h; exact ⟨h.le, h.ge⟩
      · intro h; exact le_antisymm h.1 h.2
    rw [this]
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff isOpen_setOf_valuation_lt
  · rw [val_image_unitFiltrationUnits hn hϖ]
    have : {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} =
        (Homeomorph.subRight (1 : K)) ⁻¹' {y : K | valuation K y ≤ valuation K (ϖ : K) ^ n} := by
      ext y; rfl
    rw [this, Homeomorph.isCompact_preimage]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K _

theorem exists_pow_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hz : z ≠ 0 := by rintro rfl; simp at hγ
  refine ⟨max 1 (ord z + 1).toNat, le_max_left _ _, ?_⟩
  rw [← map_pow, ← normalizedValuation_lt_iff, map_pow, normalizedValuation_uniformizer hϖ,
    normalizedValuation_eq_exp_ord hz, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_lt_neg_iff]
  have := le_max_right 1 (ord z + 1).toNat
  omega

theorem hasBasis_nhds_one_unitFiltrationUnits :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ ↦ True) (fun n ↦ (unitFiltrationUnits K n : Set Kˣ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at ht
    obtain ⟨t', ht', hsub⟩ := ht
    rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    obtain ⟨n, hn, hlt⟩ := exists_pow_lt hϖ γ.ne_zero
    refine ⟨n, trivial, fun x hx ↦ hsub (hγ ?_)⟩
    exact ((mem_unitFiltrationUnits_iff hn hϖ).mp hx).trans_lt hlt
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_unitFiltrationUnits n).mem_nhds (Subgroup.one_mem _)) hn

theorem exists_unitFiltrationUnits_le {H : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) :
    ∃ n, unitFiltrationUnits K n ≤ H := by
  obtain ⟨n, -, hn⟩ :=
    hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp (hH.mem_nhds (Subgroup.one_mem H))
  exact ⟨n, hn⟩

theorem exists_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex] :
    ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H := by
  refine ⟨H.index, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact H.pow_index_mem x

theorem exists_unitFiltrationUnits_le_and_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    (∃ n, unitFiltrationUnits K n ≤ H) ∧ ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H :=
  ⟨exists_unitFiltrationUnits_le hH, exists_range_pow_le⟩

theorem isOpen_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom m : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  refine Subgroup.isOpen_mono ?_ (isOpen_unitFiltrationUnits N)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := hN hu
  exact ⟨unitsIncl K x, by simp⟩

end GroundTheory.LocalField
end

-- bundled from GroundTheory.LocalFields.HerbrandCyclic
section
namespace GroundTheory.LocalField

open GroundTheory.GroupCoh GroundTheory.Global

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

theorem toMul_cycNorm (x : Additive M) :
    (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = tateNorm G M x.toMul := by
  rw [cycNorm_apply, toMul_sum, tateNorm_apply]
  rfl


omit [Fintype G] in
theorem toMul_cycSubOne (σ : G) (x : Additive M) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ x).toMul = σ • x.toMul / x.toMul := by
  rw [cycSubOne_apply]
  rfl

theorem ker_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).ker = (tateNorm G M).ker.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, MonoidHom.mem_ker, ← toMul_cycNorm]
  exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← toMul_zero] at h; exact Additive.toMul.injective h⟩

theorem range_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).range =
      (tateNorm G M).range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMul, (toMul_cycNorm x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨Additive.ofMul x, Additive.toMul.injective ?_⟩
    rw [toMul_cycNorm]
    exact hx

variable {σ : G}


omit [Fintype G] in
theorem ker_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker =
      (invariants G M).toAddSubgroup := by
  ext x
  rw [mem_ker_cycSubOne_iff _ hσ, Additive.mem_toAddSubgroup, mem_invariants]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  exact ⟨fun h g => congrArg Additive.toMul (h g), fun h g => by rw [h g]; rfl⟩


omit [Fintype G] in
theorem range_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range =
      (augmentation G M).toAddSubgroup := by
  rw [range_cycSubOne_eq_closure _ hσ, augmentation, Subgroup.toAddSubgroup_closure]
  congr 1

theorem natCard_tateZero_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateZero G M) =
      Nat.card (CycTateZero (Representation.ofMulDistribMulAction G M) σ) := by
  change (tateNorm G M).range.relIndex (invariants G M) =
    (cycNorm (Representation.ofMulDistribMulAction G M)).range.relIndex
      (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker
  rw [ker_cycSubOne_ofMulDistribMulAction hσ, range_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]

theorem natCard_tateNegOne_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateNegOne G M) =
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction G M) σ) := by
  change (augmentation G M).relIndex (tateNorm G M).ker =
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range.relIndex
      (cycNorm (Representation.ofMulDistribMulAction G M)).ker
  rw [range_cycSubOne_ofMulDistribMulAction hσ, ker_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]

theorem cycHerbrand_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction G M) σ =
      (Nat.card (TateZero G M) : ℚ) / Nat.card (TateNegOne G M) := by
  rw [cycHerbrand_eq, natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]

private theorem finite_iff_natCard_ne_zero {X : Type*} [Nonempty X] :
    Finite X ↔ Nat.card X ≠ 0 := by
  rw [Nat.card_ne_zero]
  exact ⟨fun h => ⟨inferInstance, h⟩, fun h => h.2⟩

theorem hasHerbrandQuotient_iff (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      Finite (TateZero G M) ∧ Finite (TateNegOne G M) := by
  rw [HasHerbrandQuotient, finite_iff_natCard_ne_zero, finite_iff_natCard_ne_zero,
    finite_iff_natCard_ne_zero (X := TateZero G M), finite_iff_natCard_ne_zero (X := TateNegOne G M),
    natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]

theorem cycHerbrand_eq_one_of_subsingleton (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    [Subsingleton (TateZero G M)] [Subsingleton (TateNegOne G M)] :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ = 1 := by
  refine ⟨(hasHerbrandQuotient_iff hσ).mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hσ, Nat.card_unique, Nat.card_unique]
  norm_num

section Injective

variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]


omit [Fintype G] in
theorem toAdditive_cycSubOne (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) (τ : G)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x) =
      cycSubOne (Representation.ofMulDistribMulAction G N) τ (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycSubOne]
  change i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x).toMul = _
  rw [toMul_cycSubOne, map_div, hi]
  rfl

theorem toAdditive_cycNorm (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycNorm (Representation.ofMulDistribMulAction G M) x) =
      cycNorm (Representation.ofMulDistribMulAction G N) (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycNorm]
  change i (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = _
  rw [toMul_cycNorm, tateNorm_apply, tateNorm_apply, map_prod]
  simp_rw [hi]
  rfl

private theorem range_toAdditive (i : M →* N) :
    (MonoidHom.toAdditive i).range = i.range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨x.toMul, by rw [← hx]; rfl⟩,
    fun ⟨x, hx⟩ => ⟨Additive.ofMul x, Additive.toMul.injective hx⟩⟩

theorem cycHerbrand_eq_of_injective (i : M →* N) (hinj : Function.Injective i)
    (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) [i.range.FiniteIndex] (τ : G) :
    (HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) τ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G N) τ)
        (cycNorm (Representation.ofMulDistribMulAction G N))) ∧
    cycHerbrand (Representation.ofMulDistribMulAction G M) τ =
      cycHerbrand (Representation.ofMulDistribMulAction G N) τ := by
  have hfi : (MonoidHom.toAdditive i).range.FiniteIndex := by
    constructor
    rw [range_toAdditive, Subgroup.index_toAddSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : Finite (Additive N ⧸ (MonoidHom.toAdditive i).range) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  have hinj' : Function.Injective (MonoidHom.toAdditive i) := hinj
  exact ⟨hasHerbrandQuotient_iff_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ),
    herbrandQuotient_eq_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ)⟩

end Injective

end GroundTheory.LocalField
end

-- bundled from GroundTheory.LocalFields.HilbertCyclic
section
namespace GroundTheory.LocalField

open Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

section Partial

variable (σ : L ≃ₐ[K] L) (x : Lˣ)

noncomputable def partialNorm (m : ℕ) : Lˣ :=
  ∏ j ∈ range m, (σ ^ j) • x

omit [FiniteDimensional K L] in
theorem partialNorm_add (a b : ℕ) :
    partialNorm σ x (a + b) = partialNorm σ x a * (σ ^ a) • partialNorm σ x b := by
  rw [partialNorm, prod_range_add, partialNorm, partialNorm, smul_prod']
  simp_rw [pow_add, mul_smul]

omit [FiniteDimensional K L] in
theorem partialNorm_one : partialNorm σ x 1 = x := by
  rw [partialNorm, prod_range_one, pow_zero, one_smul]

variable {σ}

theorem partialNorm_orderOf (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    partialNorm σ x (orderOf σ) = tateNorm (L ≃ₐ[K] L) Lˣ x := by
  rw [partialNorm, ← Fin.prod_univ_eq_prod_range, tateNorm_apply]
  refine Fintype.prod_bijective (fun j : Fin (orderOf σ) => σ ^ (j : ℕ)) ⟨?_, ?_⟩ _ _
    (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  · intro g
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    refine ⟨⟨k % orderOf σ, Nat.mod_lt _ (orderOf_pos σ)⟩, ?_⟩
    change σ ^ (k % orderOf σ) = g
    rw [pow_mod_orderOf]
    exact hk

variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx

theorem partialNorm_add_orderOf (m : ℕ) :
    partialNorm σ x (m + orderOf σ) = partialNorm σ x m := by
  rw [add_comm, partialNorm_add, partialNorm_orderOf x hσ, hx, pow_orderOf_eq_one, one_smul, one_mul]

theorem partialNorm_mod (m : ℕ) : partialNorm σ x (m % orderOf σ) = partialNorm σ x m := by
  conv_rhs => rw [← Nat.mod_add_div m (orderOf σ)]
  induction m / orderOf σ with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, partialNorm_add_orderOf hσ hx, ih]

theorem partialNorm_eq_of_pow_eq {a b : ℕ} (h : σ ^ a = σ ^ b) :
    partialNorm σ x a = partialNorm σ x b := by
  rw [← partialNorm_mod hσ hx a, ← partialNorm_mod hσ hx b, (pow_eq_pow_iff_modEq.mp h)]

end Partial

theorem exists_smul_div_eq_of_tateNorm_eq_one {σ : L ≃ₐ[K] L}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : Lˣ} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, σ • y / y = x := by
  have hk : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g := fun g => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    exact ⟨k, hk⟩
  choose k hk using hk
  let f : (L ≃ₐ[K] L) → Lˣ := fun g => partialNorm σ x (k g)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    have e : σ ^ k (g * h) = σ ^ (k g + k h) := by rw [hk, pow_add, hk, hk]
    change partialNorm σ x (k (g * h)) = g • partialNorm σ x (k h) * partialNorm σ x (k g)
    rw [partialNorm_eq_of_pow_eq hσ hx e, partialNorm_add, hk, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, ?_⟩
  rw [hβ σ]
  change partialNorm σ x (k σ) = x
  rw [partialNorm_eq_of_pow_eq hσ hx (show σ ^ k σ = σ ^ 1 by rw [hk, pow_one]), partialNorm_one]

theorem subsingleton_tateNegOne_units [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) Lˣ) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hσ hx
  exact Subgroup.subset_closure ⟨σ, y, hy⟩

end GroundTheory.LocalField
end

