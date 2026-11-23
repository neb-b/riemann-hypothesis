module

public import Mathlib
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Bundle0002
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.Bundle0004
public import GroundTheory.LocalFields.UnramifiedGalois
public import GroundTheory.LocalFields.Bundle0006
public import GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.LocalFields.CompleteTrivial
public import GroundTheory.LocalFields.Bundle0003

@[expose] public section

-- bundled from GroundTheory.LocalFields.UnramifiedExistence
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IntermediateField

section Card

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem card_residueField_of_unramified (h : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1) :
    Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ Module.finrank K L := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[L]
  rw [← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])]

end Card

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem adjoin_gen_eq_top (α : Ksep) : K⟮AdjoinSimple.gen K α⟯ = ⊤ := by
  apply map_injective K⟮α⟯.val
  rw [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]
  exact congrArg (fun x ↦ K⟮x⟯) (AdjoinSimple.coe_gen K α)

def IsUnramifiedSubextension (E : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1

theorem isUnramifiedSubextension_iff_exists (E : IntermediateField K Ksep) :
    IsUnramifiedSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem IsUnramifiedSubextension.ramificationIndex_eq_one {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  hE.2 inferInstance inferInstance inferInstance inferInstance

theorem IsUnramifiedSubextension.isGalois {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsGalois K E := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isGalois_of_unramified K E hE.ramificationIndex_eq_one

theorem IsUnramifiedSubextension.isCyclic {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsCyclic (E ≃ₐ[K] E) := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isCyclic_of_unramified K E hE.ramificationIndex_eq_one

theorem IsUnramifiedSubextension.card_algEquiv {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
  have := hE.1
  have := hE.isGalois
  exact IsGalois.card_aut_eq_finrank K E

theorem exists_isPrimitiveRoot_card_pow_sub_one [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : Ksep, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  have hK := natCast_ne_zero_of_residueField (natCast_card_pow_sub_one_ne_zero (K := K) hn)
  have : NeZero ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).mpr hK⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ksep _

theorem isUnramifiedSubextension_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n := by
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hpos : 0 < Nat.card 𝓀[K] ^ n - 1 := by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega
  have hint : IsIntegral K ζ := (hζ.isIntegral hpos).tower_top
  have hfin : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hint
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  have htop := adjoin_gen_eq_top (K := K) ζ
  refine ⟨⟨hfin, fun _ _ _ _ ↦ ramificationIndex_eq_one_of_adjoin_eq_top hζ' hm htop⟩, ?_⟩
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  exact finrank_eq_of_adjoin_eq_top hn hζ' htop

theorem IsUnramifiedSubextension.eq_adjoin {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hEn : Module.finrank K E = n) (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E = K⟮ζ⟯ := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  have h := hE.ramificationIndex_eq_one
  obtain ⟨ξ, hξ, -⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K E h
  rw [card_residueField_of_unramified K E h, hEn] at hξ
  have hξ' : IsPrimitiveRoot (ξ : Ksep) (Nat.card 𝓀[K] ^ n - 1) :=
    hξ.map_of_injective (f := E.val) Subtype.val_injective
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega⟩
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hζE : ζ ∈ E := hi ▸ pow_mem ξ.2 i
  have hle : K⟮ζ⟯ ≤ E := adjoin_simple_le_iff.mpr hζE
  refine (eq_of_le_of_finrank_eq hle ?_).symm
  rw [(isUnramifiedSubextension_adjoin hn hζ).2, hEn]

theorem existsUnique_isUnramifiedSubextension [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃! E : IntermediateField K Ksep, IsUnramifiedSubextension E ∧ Module.finrank K E = n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ksep) hn
  exact ⟨K⟮ζ⟯, isUnramifiedSubextension_adjoin hn hζ,
    fun E ⟨hE, hEn⟩ ↦ hE.eq_adjoin hEn hn hζ⟩

theorem isUnramifiedSubextension_adjoin_spec {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n ∧ IsGalois K K⟮ζ⟯ ∧
      IsCyclic (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) ∧ Nat.card (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) = n ∧
      ∀ E : IntermediateField K Ksep, IsUnramifiedSubextension E → Module.finrank K E = n →
        E = K⟮ζ⟯ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  exact ⟨hE, hEn, hE.isGalois, hE.isCyclic, hE.card_algEquiv.trans hEn,
    fun E hE' hE'n ↦ hE'.eq_adjoin hE'n hn hζ⟩

variable {E : IntermediateField K Ksep} (hE : IsUnramifiedSubextension E)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
include hE

end SeparableClosure

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.UnramifiedNorms
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem coe_tateNorm_integerUnits [IsGalois K L] (u : 𝒪[L]ˣ) :
    (((tateNorm (L ≃ₐ[K] L) 𝒪[L]ˣ u : 𝒪[L]ˣ) : 𝒪[L]) : L) =
      algebraMap K L (Algebra.norm K ((u : 𝒪[L]) : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, tateNorm_apply, Units.coe_prod]
  push_cast
  rfl

theorem exists_eq_of_forall_smul_eq [IsGalois K L] {x : 𝒪[L]ˣ}
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) :
    ∃ w : 𝒪[K]ˣ, algebraMap K L ((w : 𝒪[K]) : K) = ((x : 𝒪[L]) : L) := by
  have hfix : ((x : 𝒪[L]) : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed _).2 fun σ ↦ by
      have := congrArg (fun u : 𝒪[L]ˣ ↦ ((u : 𝒪[L]) : L)) (hx σ)
      change σ ((x : 𝒪[L]) : L) = ((x : 𝒪[L]) : L) at this
      exact this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (Units.ne_zero x) (by exact_mod_cast hc.symm)
  have h1 : c ∈ 𝒪[K] := (algebraMap_mem_integer_iff K L c).1 (hc ▸ (x : 𝒪[L]).2)
  have h2 : c⁻¹ ∈ 𝒪[K] := by
    refine (algebraMap_mem_integer_iff K L c⁻¹).1 ?_
    have e : algebraMap K L c⁻¹ = (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
      rw [map_inv₀, hc, eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (Units.ne_zero x))]
      exact_mod_cast congrArg (fun u : 𝒪[L] ↦ (u : L)) x.inv_mul
    rw [e]
    exact (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L])).2
  refine ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, ?_, ?_⟩, hc⟩
  · ext
    simp [hc0]
  · ext
    simp [hc0]

theorem subsingleton_tateZero_integerUnits [IsGalois K L] [IsUnramified K L] :
    Subsingleton (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  obtain ⟨w, hw⟩ := exists_eq_of_forall_smul_eq (K := K) (L := L) hx
  obtain ⟨v, rfl⟩ := normIntegerUnits_surjective (K := K) (L := L) w
  refine ⟨v, Units.ext (Subtype.ext ?_)⟩
  rw [coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]

theorem subsingleton_tateNegOne_integerUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramified K L] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hxL : tateNorm (L ≃ₐ[K] L) Lˣ (unitsIncl L x) = 1 := by
    rw [tateNorm_apply]
    simp_rw [← unitsIncl_smul]
    rw [← map_prod, ← tateNorm_apply, hx, map_one]
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hg hxL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨⟨m, v⟩, rfl⟩ := (unitsOfIntProd_bijective hϖL).2 y
  have hπ : g • uniformizerUnit hϖL = uniformizerUnit hϖL := by
    ext
    change g ((uniformizerUnit hϖL : Lˣ) : L) = _
    rw [coe_uniformizerUnit, coe_algebraMap_integer, AlgEquiv.commutes]
  have hx' : x = g • v / v := by
    apply unitsIncl_injective (K := L)
    rw [← hy, unitsOfIntProd_eq, _root_.map_div, unitsIncl_smul, smul_mul', smul_zpow', hπ,
      mul_div_mul_left_eq_div]
  rw [hx']
  exact Subgroup.subset_closure ⟨g, v, rfl⟩

end GroundTheory.LocalField
end
end

