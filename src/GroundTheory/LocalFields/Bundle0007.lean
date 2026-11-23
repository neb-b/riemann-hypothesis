module

public import Mathlib
public import GroundTheory.LocalFields.Bundle0005
public import GroundTheory.LocalFields.CompleteTrivialLocal
public import GroundTheory.LocalFields.Bundle0006
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.IntermediateField
public import GroundTheory.LocalFields.Bundle0004
public import GroundTheory.LocalFields.UnramifiedHensel

@[expose] public section

-- bundled from GroundTheory.LocalFields.HerbrandLocal
section
namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] in
theorem finiteIndex_of_isOpen_integerUnits {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

theorem cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))

theorem cycHerbrand_units_eq_finrank (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        Module.finrank K L := by
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hσ
  obtain ⟨hB, h2⟩ := cycHerbrand_units_eq_mul hσ hA
  refine ⟨hB, ?_⟩
  rw [h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

variable [IsCyclic (L ≃ₐ[K] L)]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in
theorem natCard_tateNegOne_units : Nat.card (TateNegOne (L ≃ₐ[K] L) Lˣ) = 1 := by
  have := subsingleton_tateNegOne_units (K := K) (L := L)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem natCard_tateZero_units :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h

theorem natCard_units_quotient_range_normUnits :
    Nat.card (Kˣ ⧸ (normUnits K L).range) = Module.finrank K L := by
  rw [← natCard_tateZero_units_eq]
  exact natCard_tateZero_units

end GroundTheory.LocalField
end

-- bundled from GroundTheory.LocalFields.RamificationStructure
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Tame

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

def inertiaToResidueUnits : lowerRamificationGroup K L 0 →* 𝓀[L]ˣ where
  toFun σ := unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L))
  map_one' := by simp
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, uniformizerRatio_mul, map_mul]
    congr 1
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L σ.2 _

theorem inertiaToResidueUnits_apply (σ : lowerRamificationGroup K L 0) :
    inertiaToResidueUnits hϖ σ = unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L)) :=
  rfl

theorem ker_inertiaToResidueUnits :
    (inertiaToResidueUnits hϖ).ker =
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, inertiaToResidueUnits_apply,
    ← MonoidHom.mem_ker, ker_unitsToResidue]
  exact (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ σ.2 1).symm

def inertiaQuotientToResidueUnits :
    lowerRamificationGroup K L 0 ⧸
        (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) →* 𝓀[L]ˣ :=
  (QuotientGroup.kerLift (inertiaToResidueUnits hϖ)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_inertiaToResidueUnits hϖ).symm).toMonoidHom

theorem inertiaQuotientToResidueUnits_injective :
    Function.Injective (inertiaQuotientToResidueUnits (K := K) hϖ) :=
  fun _ _ hab ↦ (MulEquiv.injective _) (QuotientGroup.kerLift_injective (inertiaToResidueUnits hϖ) hab)

omit hϖ

variable (K L)

theorem isCyclic_lowerRamificationGroup_zero_quotient :
    IsCyclic (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  exact isCyclic_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

theorem card_lowerRamificationGroup_zero_quotient_dvd :
    Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) ∣
        Nat.card 𝓀[L] - 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units 𝓀[L]]
  exact Subgroup.card_dvd_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

variable {K L}

theorem coprime_card_residueField_sub_one : Nat.Coprime (Nat.card 𝓀[L] - 1) (ringChar 𝓀[L]) := by
  let := Fintype.ofFinite 𝓀[L]
  have hq : ringChar 𝓀[L] ∣ Nat.card 𝓀[L] := by
    rw [← CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have h1 : 1 ≤ Nat.card 𝓀[L] := Nat.card_pos
  refine Nat.Coprime.symm (Nat.dvd_one.mp ?_)
  have ha := Nat.gcd_dvd_left (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have hb := Nat.gcd_dvd_right (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have := Nat.dvd_sub (ha.trans hq) hb
  rwa [Nat.sub_sub_self h1] at this

variable (K L)

theorem coprime_card_lowerRamificationGroup_zero_quotient :
    Nat.Coprime (Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0))) (ringChar 𝓀[K]) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  exact Nat.Coprime.coprime_dvd_left (card_lowerRamificationGroup_zero_quotient_dvd K L)
    coprime_card_residueField_sub_one

end Tame

section Wild

theorem pow_ringChar_eq_one_unitFiltration {n : ℕ} (hn : 1 ≤ n)
    (y : unitFiltration L n ⧸ unitFiltrationSucc L n) : y ^ ringChar 𝓀[L] = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  apply (unitFiltrationGradedEquiv hϖ hn).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

theorem pow_ringChar_mem_lowerRamificationGroup {n : ℕ} (hn : 1 ≤ n) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L n) :
    σ ^ ringChar 𝓀[L] ∈ lowerRamificationGroup K L (n + 1 : ℕ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have h : ((⟨σ, hσ⟩ : lowerRamificationGroup K L n) ^ ringChar 𝓀[L]) ∈
      (ramificationToUnits hϖ n).ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_ringChar_eq_one_unitFiltration hn]
  rw [ker_ramificationToUnits, Subgroup.mem_subgroupOf] at h
  simpa using h

variable (K L)

theorem isPGroup_lowerRamificationGroup_one :
    IsPGroup (ringChar 𝓀[K]) (lowerRamificationGroup K L 1) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have key : ∀ k : ℕ, ∀ σ ∈ lowerRamificationGroup K L 1,
      σ ^ (ringChar 𝓀[L] ^ k) ∈ lowerRamificationGroup K L ((1 + k : ℕ) : ℤ) := by
    intro k σ hσ
    induction k with
    | zero => simpa using hσ
    | succ k ih =>
      rw [pow_succ, pow_mul, show 1 + (k + 1) = 1 + k + 1 by omega]
      exact pow_ringChar_mem_lowerRamificationGroup (by omega) ih
  intro σ
  refine ⟨N, Subtype.ext ?_⟩
  have := key N σ σ.2
  rw [hN _ (by omega), Subgroup.mem_bot] at this
  simpa using this

theorem isSolvable_lowerRamificationGroup_one : Group.IsSolvable (lowerRamificationGroup K L 1) := by
  have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  have := (isPGroup_lowerRamificationGroup_one K L).isNilpotent
  infer_instance

theorem isSolvable_lowerRamificationGroup_zero : Group.IsSolvable (lowerRamificationGroup K L 0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have := isSolvable_lowerRamificationGroup_one K L
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (lowerRamificationGroup_antitone K L zero_le_one))
    (inertiaToResidueUnits hϖ) ?_
  intro σ hσ
  rw [ker_inertiaToResidueUnits, Subgroup.mem_subgroupOf] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

theorem isSolvable_algEquiv : Group.IsSolvable (L ≃ₐ[K] L) := by
  have := isSolvable_lowerRamificationGroup_zero K L
  have : Group.IsSolvable (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
    Group.isSolvable_of_comm fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  refine Group.isSolvable_of_ker_le_range (lowerRamificationGroup K L 0).subtype (residueAlgEquiv K L) ?_
  intro σ hσ
  rw [← lowerRamificationGroup_zero] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

end Wild

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.Unramified
section
noncomputable section

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

namespace GroundTheory.LocalField

section Generator

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnit_aeval_derivative_of_separable (P : 𝒪[K][X])
    (hP : (P.map (residue 𝒪[K])).Separable) (x : 𝒪[L]) (hx : aeval x P = 0) :
    IsUnit (aeval x (derivative P)) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval K L (fun _ ↦ rfl), ← derivative_map]
  refine hP.aeval_derivative_ne_zero ?_
  rw [← residue_aeval K L (fun _ ↦ rfl), hx, map_zero]

theorem IsUnramified.exists_generator [IsUnramified K L] :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnit (aeval β (derivative P)) ∧ K⟮(β : L)⟯ = ⊤ := by
  obtain ⟨β, P, hPm, hβ, hsep, -, hdeg, -⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, hsep, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_⟩
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [hdeg, IntermediateField.finrank_top', IsUnramified.residueDegree_eq_finrank K L]

end Generator

section Etale

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem map_maximalIdeal_eq_iff :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) = maximalIdeal 𝒪[L] ↔ IsUnramified K L := by
  rw [map_maximalIdeal K L, isUnramified_iff]
  change maximalIdeal 𝒪[L] ^ ramificationIndex K L = maximalIdeal 𝒪[L] ↔
    ramificationIndex K L = 1
  constructor
  · intro h
    have hpos := ramificationIndex_pos K L
    by_contra hne
    have h2 : 2 ≤ ramificationIndex K L := by omega
    have hL : maximalIdeal 𝒪[L] ≠ ⊥ := maximalIdeal_ne_bot L
    have hlt := Ideal.pow_succ_lt_pow hL 1
    have hle : maximalIdeal 𝒪[L] ^ 1 ≤ maximalIdeal 𝒪[L] ^ (1 + 1) :=
      calc maximalIdeal 𝒪[L] ^ 1 = maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
            rw [pow_one, h]
        _ ≤ maximalIdeal 𝒪[L] ^ (1 + 1) := Ideal.pow_le_pow_right h2
    exact absurd hle (not_le_of_gt hlt)
  · intro h
    rw [h, pow_one]

end Etale

section Maximal

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

def maximalUnramified : IntermediateField K L :=
  sSup {E : IntermediateField K L | IsUnramified K E}

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]


theorem exists_generator_of_isUnramified (E : IntermediateField K L) [IsUnramified K E] :
    ∃ (γ : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval γ P = 0 ∧ IsUnit (aeval γ (derivative P)) ∧
      E = K⟮(γ : L)⟯ := by
  obtain ⟨β, P, hPm, hβ, -, hd, htop⟩ := IsUnramified.exists_generator K E
  refine ⟨algebraMap 𝒪[E] 𝒪[L] β, P, hPm, ?_, ?_, ?_⟩
  · rw [aeval_algebraMap_apply, hβ, map_zero]
  · rw [aeval_algebraMap_apply]
    exact hd.map _
  · have := congrArg (IntermediateField.map E.val) htop
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this.symm

theorem exists_maximalUnramified_eq :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ IsUnit (aeval β (derivative P)) ∧
      maximalUnramified K L = K⟮(β : L)⟯ ∧ IsUnramified K K⟮(β : L)⟯ ∧
      Module.finrank K K⟮(β : L)⟯ = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K⟮(β : L)⟯])) = 1 := by
  obtain ⟨β, P, hPm, hβ, hsep, hunr, hdeg, h1⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_, hunr, hdeg, h1⟩
  refine le_antisymm (sSup_le fun E hE ↦ ?_) (le_sSup hunr)
  have : IsUnramified K E := hE
  obtain ⟨γ, Q, hQ, hγ, hd, hE'⟩ := exists_generator_of_isUnramified K L E
  rw [hE']
  exact IntermediateField.adjoin_simple_le_iff.2 (mem_of_residueDegree_eq_one K L _ h1 Q hQ γ hγ hd)

theorem finrank_maximalUnramified :
    Module.finrank K (maximalUnramified K L) = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
  obtain ⟨β, P, -, -, -, heq, -, hdeg, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hdeg

end Maximal

section BaseChange

variable (K K' L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
  [ValuativeExtension K K'] [ValuativeExtension K' L] [ValuativeExtension K L]
  [FiniteDimensional K L]

end BaseChange

section Galois

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def inertiaSubgroup : Subgroup (L ≃ₐ[K] L) := (residueAlgEquiv K L).ker

theorem inertiaSubgroup_apply_eq (σ : L ≃ₐ[K] L) (hσ : σ ∈ inertiaSubgroup K L) (P : 𝒪[K][X])
    (γ : 𝒪[L]) (hγ : aeval γ P = 0) (hd : IsUnit (aeval γ (derivative P))) : σ γ = γ := by
  set γσ := integerAlgEquiv K L σ γ
  have h0 : aeval γσ P = 0 := by
    have := aeval_algHom_apply (integerAlgEquiv K L σ : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) γ P
    rw [hγ, map_zero] at this
    exact this
  have hres : residue 𝒪[L] γσ = residue 𝒪[L] γ := by
    have h1 : residueAlgEquiv K L σ = 1 := hσ
    rw [← residueAlgEquiv_residue, h1]
    rfl
  have heq : γ = γσ := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact h0) ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [← coe_integerAlgEquiv_apply]
  exact congrArg Subtype.val heq.symm

theorem maximalUnramified_le_fixedField :
    maximalUnramified K L ≤ IntermediateField.fixedField (inertiaSubgroup K L) := by
  obtain ⟨β, P, -, hβ, hd, heq, -, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq, IntermediateField.adjoin_simple_le_iff]
  exact fun σ ↦ inertiaSubgroup_apply_eq K L σ σ.2 P β hβ hd

variable [IsGalois K L]

theorem inertiaSubgroup_counting :
    Nat.card (inertiaSubgroup K L) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) ∧
      Nat.card (residueAlgEquiv K L).range = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧
      Module.finrank K (IntermediateField.fixedField (inertiaSubgroup K L)) = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
  set I := inertiaSubgroup K L
  set F := IntermediateField.fixedField I
  have hn := ramificationIndex_mul_residueDegree K L
  have hf := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hFL : Module.finrank F L = Nat.card I := IntermediateField.finrank_fixedField_eq_card I
  have hG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hIdx : Nat.card I * I.index = Nat.card (L ≃ₐ[K] L) := Subgroup.card_mul_index I
  have hind : I.index = Nat.card (residueAlgEquiv K L).range := Subgroup.index_ker _
  have hrange : Nat.card (residueAlgEquiv K L).range ≤ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
    calc Nat.card (residueAlgEquiv K L).range ≤ Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
          Subgroup.card_le_card_group _
      _ = Module.finrank 𝓀[K] 𝓀[L] := IsGalois.card_aut_eq_finrank _ _
      _ = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := (residueDegree_eq_finrank K L).symm
  have hFK : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
    Module.finrank_mul_finrank K F L
  have hTF : ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ≤ Module.finrank K F := by
    rw [← finrank_maximalUnramified K L]
    exact IntermediateField.finrank_le_of_le_right (maximalUnramified_le_fixedField K L)
  set a := Nat.card I
  set r := Nat.card (residueAlgEquiv K L).range
  set e := (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K)))
  set f := ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K]))
  set d := Module.finrank K F
  rw [hind, hG, ← hn] at hIdx
  rw [hFL, ← hn] at hFK
  have h1 : a ≤ e := by
    refine Nat.le_of_mul_le_mul_left ?_ hf
    calc f * a ≤ d * a := Nat.mul_le_mul_right _ hTF
      _ = e * f := hFK
      _ = f * e := mul_comm _ _
  have h2 : e ≤ a := by
    refine Nat.le_of_mul_le_mul_right ?_ hf
    calc e * f = a * r := hIdx.symm
      _ ≤ a * f := Nat.mul_le_mul_left _ hrange
  have hae : a = e := le_antisymm h1 h2
  refine ⟨hae, ?_, ?_⟩
  · rw [hae] at hIdx
    exact (Nat.eq_of_mul_eq_mul_left he hIdx)
  · rw [hae, mul_comm e f] at hFK
    exact Nat.eq_of_mul_eq_mul_right he hFK

theorem card_inertiaSubgroup : Nat.card (inertiaSubgroup K L) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) :=
  (inertiaSubgroup_counting K L).1

end Galois

end GroundTheory.LocalField
end
end

