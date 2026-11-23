module

public import Mathlib
public import GroundTheory.LocalFields.Ramification
public import GroundTheory.LocalFields.Bundle0004
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.LocalFields.Bundle0001
public import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

-- bundled from GroundTheory.LocalFields.RamificationUnits
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Inertia

theorem integerAlgEquiv_teichmuller {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (ζ : 𝓀[L]ˣ) :
    integerAlgEquiv K L σ (teichmuller L ζ : 𝒪[L]) = teichmuller L ζ := by
  have hres : unitsToResidue L (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])
      (teichmuller L ζ)) = unitsToResidue L (teichmuller L ζ) := by
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L hσ _
  have hpow : Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (teichmuller L ζ) ^
      (Nat.card 𝓀[L] - 1) = 1 := by
    rw [← map_pow, teichmuller_pow_card_sub_one, map_one]
  exact congrArg Units.val (eq_of_pow_card_sub_one hpow (teichmuller_pow_card_sub_one ζ) hres)

theorem sub_mem_of_uniformizer {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {n : ℕ}
    (h : integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ n) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ n := by
  set e := integerAlgEquiv K L σ
  let P : 𝒪[L] → Prop := fun y ↦ e y - y ∈ 𝓂[L] ^ n
  have hadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb ↦ by
    have : e (a + b) - (a + b) = (e a - a) + (e b - b) := by rw [map_add (f := _)]; ring
    simp only [P, this]
    exact add_mem ha hb
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb ↦ by
    have : e (a * b) - a * b = e a * (e b - b) + (e a - a) * b := by rw [map_mul]; ring
    simp only [P, this]
    exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
  have hpow : ∀ a (k : ℕ), P a → P (a ^ k) := by
    intro a k ha
    induction k with
    | zero => simp [P]
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih ha
  have hfix : ∀ a, e a = a → P a := fun a ha ↦ by simp [P, ha]
  have hideal : ∀ y ∈ 𝓂[L] ^ n, P y := fun y hy ↦
    sub_mem ((integerAlgEquiv_mem_maximalIdeal_pow_iff σ n y).mpr hy) hy
  have happrox : ∀ y : 𝒪[L], ∃ t, e t = t ∧ y - t ∈ 𝓂[L] := by
    intro y
    by_cases hy : residue 𝒪[L] y = 0
    · exact ⟨0, map_zero e, by simpa using (residue_eq_zero_iff y).mp hy⟩
    · refine ⟨teichmuller L (Units.mk0 _ hy), integerAlgEquiv_teichmuller hσ _, ?_⟩
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrArg Units.val (unitsToResidue_teichmuller (K := L) (Units.mk0 _ hy))).symm
  have hstep : ∀ m : ℕ, ∃ r, P r ∧ x - r ∈ 𝓂[L] ^ m := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp [P], by simp⟩
    | succ m ih =>
      obtain ⟨r, hr, hxr⟩ := ih
      obtain ⟨y, hy⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hxr
      obtain ⟨t, ht, hyt⟩ := happrox y
      obtain ⟨z, hz⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hyt
      refine ⟨r + ϖ ^ m * t, hadd _ _ hr (hmul _ _ (hpow _ _ h) (hfix _ ht)), ?_⟩
      rw [mem_maximalIdeal_pow_iff hϖ]
      exact ⟨z, by rw [pow_succ]; linear_combination hy + ϖ ^ m * hz⟩
  obtain ⟨r, hr, hxr⟩ := hstep n
  have : x = r + (x - r) := by ring
  rw [this]
  exact hadd _ _ hr (hideal _ hxr)

theorem mem_lowerRamificationGroup_iff_uniformizer {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) :=
  ⟨fun h ↦ mem_lowerRamificationGroup_natCast_iff.mp h ϖ,
    fun h ↦ mem_lowerRamificationGroup_natCast_iff.mpr (sub_mem_of_uniformizer hσ hϖ h)⟩

end Inertia

section Ratio

theorem irreducible_integerAlgEquiv (σ : L ≃ₐ[K] L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Irreducible (integerAlgEquiv K L σ ϖ) :=
  (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ

def uniformizerRatio {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (σ : L ≃ₐ[K] L) : 𝒪[L]ˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

theorem mul_uniformizerRatio (σ : L ≃ₐ[K] L) :
    ϖ * uniformizerRatio hϖ σ = integerAlgEquiv K L σ ϖ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose_spec

theorem uniformizerRatio_eq_iff (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    uniformizerRatio hϖ σ = u ↔ ϖ * u = integerAlgEquiv K L σ ϖ := by
  refine ⟨fun h ↦ h ▸ mul_uniformizerRatio hϖ σ, fun h ↦ Units.ext ?_⟩
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans h.symm)

@[simp]
theorem uniformizerRatio_one : uniformizerRatio hϖ (1 : L ≃ₐ[K] L) = 1 := by
  rw [uniformizerRatio_eq_iff, map_one, AlgEquiv.one_apply, Units.val_one, mul_one]

theorem uniformizerRatio_mul (σ τ : L ≃ₐ[K] L) :
    uniformizerRatio hϖ (σ * τ) = uniformizerRatio hϖ σ *
      Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (uniformizerRatio hϖ τ) := by
  rw [uniformizerRatio_eq_iff, map_mul, AlgEquiv.mul_apply, ← mul_uniformizerRatio hϖ τ, map_mul,
    ← mul_uniformizerRatio hϖ σ, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, mul_assoc]

theorem mem_lowerRamificationGroup_iff_uniformizerRatio {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ uniformizerRatio hϖ σ ∈ unitFiltration L n := by
  rw [mem_lowerRamificationGroup_iff_uniformizer hσ hϖ, mem_unitFiltration,
    ← mul_uniformizerRatio hϖ σ, mem_maximalIdeal_pow_iff hϖ, mem_maximalIdeal_pow_iff hϖ,
    show ϖ * (uniformizerRatio hϖ σ : 𝒪[L]) - ϖ = ϖ * ((uniformizerRatio hϖ σ : 𝒪[L]) - 1) by ring,
    pow_succ', mul_dvd_mul_iff_left hϖ.ne_zero]

theorem uniformizerRatio_mem {n : ℕ} (σ : lowerRamificationGroup K L n) :
    uniformizerRatio hϖ (σ : L ≃ₐ[K] L) ∈ unitFiltration L n :=
  (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ
    (lowerRamificationGroup_antitone K L (by omega) σ.2) n).mp σ.2


omit hϖ in
theorem map_mul_inv_mem {n : ℕ} {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L n)
    (u : 𝒪[L]ˣ) :
    Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ ∈ unitFiltration L (n + 1) := by
  rw [mem_unitFiltration]
  have h : ((Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 =
      (integerAlgEquiv K L σ u - u) * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) := by
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, sub_mul, Units.mul_inv]
  rw [h]
  exact Ideal.mul_mem_right _ _ (mem_lowerRamificationGroup_natCast_iff.mp hσ (u : 𝒪[L]))


omit hϖ in
abbrev unitFiltrationSucc (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) : Subgroup (unitFiltration L n) :=
  (unitFiltration L (n + 1)).subgroupOf (unitFiltration L n)

def ramificationToUnits (n : ℕ) :
    lowerRamificationGroup K L n →* unitFiltration L n ⧸ unitFiltrationSucc L n where
  toFun σ := QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩
  map_one' := by
    have : (⟨uniformizerRatio hϖ ((1 : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
      uniformizerRatio_mem hϖ 1⟩ : unitFiltration L n) = 1 := Subtype.ext (uniformizerRatio_one hϖ)
    rw [this, QuotientGroup.mk_one]
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := map_mul_inv_mem σ.2 (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))
    have key : (((⟨uniformizerRatio hϖ ((σ * τ : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
        uniformizerRatio_mem hϖ (σ * τ)⟩ : unitFiltration L n)⁻¹ *
        (⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ *
          ⟨uniformizerRatio hϖ (τ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ τ⟩) : unitFiltration L n) : 𝒪[L]ˣ) =
        (Units.map (integerAlgEquiv K L (σ : L ≃ₐ[K] L) : 𝒪[L] →* 𝒪[L])
          (uniformizerRatio hϖ (τ : L ≃ₐ[K] L)) * (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, uniformizerRatio_mul]
      group
      exact mul_comm _ _
    rw [key]
    exact inv_mem h

theorem ramificationToUnits_apply (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationToUnits hϖ n σ =
      QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ :=
  rfl

theorem ker_ramificationToUnits (n : ℕ) :
    (ramificationToUnits hϖ n).ker =
      (lowerRamificationGroup K L (n + 1 : ℕ)).subgroupOf (lowerRamificationGroup K L n) := by
  ext σ
  have hσ0 : (σ : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 :=
    lowerRamificationGroup_antitone K L (by omega) σ.2
  rw [MonoidHom.mem_ker, ramificationToUnits_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_lowerRamificationGroup_iff_uniformizerRatio hϖ hσ0]

end Ratio

end GroundTheory.LocalField
end
end

-- bundled from GroundTheory.LocalFields.UnramifiedNormSurj
section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Filter Polynomial
open GroundTheory.Global (filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
  div_mem_unitFiltration_iff)

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in
theorem coe_normIntegerUnits_eq (u : 𝒪[L]ˣ) :
    ((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) = Algebra.norm 𝒪[K] (u : 𝒪[L]) :=
  rfl

theorem exists_norm_one_add_smul (r : 𝒪[K]) (a : 𝒪[L]) :
    ∃ c : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • a) =
      1 + r * Algebra.trace 𝒪[K] 𝒪[L] a + r ^ 2 * c := by
  classical
  let b := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  refine ⟨(Matrix.det (1 + (X : 𝒪[K][X]) • (Algebra.leftMulMatrix b a).map C)).divX.divX.eval r,
    ?_⟩
  rw [Algebra.norm_eq_matrix_det b, map_add (f := _), map_one, map_smul, Matrix.det_one_add_smul,
    Algebra.trace_eq_matrix_trace b]
  ring

theorem residue_eq_sum_repr (y : 𝒪[L]) :
    residue 𝒪[L] y = ∑ i, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) •
      residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  conv_lhs => rw [← (Module.Free.chooseBasis 𝒪[K] 𝒪[L]).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  rfl

section Residue

variable [IsUnramified K L]


variable (K L) in
def residueBasis : Module.Basis (Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) 𝓀[K] 𝓀[L] :=
  basisOfTopLeSpanOfCardEqFinrank (fun i ↦ residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i))
    (by
      rintro z -
      obtain ⟨y, rfl⟩ := residue_surjective z
      rw [residue_eq_sum_repr (K := K)]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_integer K L,
        IsUnramified.finrank_residueField K L])

theorem residueBasis_apply (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    residueBasis K L i = residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  simp [residueBasis]

theorem residueBasis_repr (y : 𝒪[L]) (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    (residueBasis K L).repr (residue 𝒪[L] y) i =
      residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) := by
  have h : residue 𝒪[L] y = ∑ j, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y j) •
      residueBasis K L j := by
    simp only [residueBasis_apply]
    exact residue_eq_sum_repr y
  rw [h, (residueBasis K L).repr_sum_self]

theorem leftMulMatrix_residueBasis (y : 𝒪[L]) :
    Algebra.leftMulMatrix (residueBasis K L) (residue 𝒪[L] y) =
      (Algebra.leftMulMatrix (Module.Free.chooseBasis 𝒪[K] 𝒪[L]) y).map (residue 𝒪[K]) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    residueBasis_apply, ← map_mul, residueBasis_repr]

theorem residue_norm (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.norm 𝒪[K] y) = Algebra.norm 𝓀[K] (residue 𝒪[L] y) := by
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.norm_eq_matrix_det (residueBasis K L), leftMulMatrix_residueBasis, RingHom.map_det]
  rfl

theorem residue_trace (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.trace 𝒪[K] 𝒪[L] y) = Algebra.trace 𝓀[K] 𝓀[L] (residue 𝒪[L] y) := by
  rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.trace_eq_matrix_trace (residueBasis K L), leftMulMatrix_residueBasis]
  exact AddMonoidHom.map_trace (residue 𝒪[K]).toAddMonoidHom _

theorem irreducible_algebraMap_of_isUnramified {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  have h := map_maximalIdeal K L
  rw [ramificationIndex, IsUnramified.ramificationIndex_eq_one, pow_one, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton] at h
  exact h.symm

theorem trace_integer_surjective : Function.Surjective (Algebra.trace 𝒪[K] 𝒪[L]) := by
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] 1
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] a) := by
    rw [← residue_ne_zero_iff_isUnit, residue_trace, ht]
    exact one_ne_zero
  intro c
  refine ⟨(((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) • a, ?_⟩
  rw [map_smul, smul_eq_mul]
  linear_combination c * Units.inv_mul hu.unit - (((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) * hu.unit_spec

theorem normIntegerUnits_mem_unitFiltration {n : ℕ} {u : 𝒪[L]ˣ} (hu : u ∈ unitFiltration L n) :
    normIntegerUnits K L u ∈ unitFiltration K n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖL).mp (mem_unitFiltration.mp hu)
  have hu' : (u : 𝒪[L]) = 1 + ϖ ^ n • a := by
    rw [Algebra.smul_def, map_pow, ← ha]
    ring
  obtain ⟨c, hc⟩ := exists_norm_one_add_smul (ϖ ^ n) a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  refine ⟨Algebra.trace 𝒪[K] 𝒪[L] a + ϖ ^ n * c, ?_⟩
  rw [coe_normIntegerUnits_eq, hu', hc]
  ring

theorem exists_normIntegerUnits_div_mem_one (h : 𝒪[K]ˣ) :
    ∃ g : 𝒪[L]ˣ, h / normIntegerUnits K L g ∈ unitFiltration K 1 := by
  obtain ⟨ζ, hζ⟩ := FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L] (unitsToResidue K h)
  obtain ⟨g, rfl⟩ := unitsToResidue_surjective L ζ
  refine ⟨g, ?_⟩
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, _root_.map_div, div_eq_one, ← hζ]
  ext
  simp [coe_normIntegerUnits_eq, residue_norm]

theorem exists_normIntegerUnits_div_mem_succ {n : ℕ} (hn : 1 ≤ n) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K n) :
    ∃ g ∈ unitFiltration L n, h / normIntegerUnits K L g ∈ unitFiltration K (n + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hh)
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] (residue 𝒪[K] c)
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu := isUnit_one_add_mul hϖL hn a
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖL]
    exact dvd_mul_right _ _
  · rw [div_mem_unitFiltration_iff]
    obtain ⟨d, hd⟩ := exists_norm_one_add_smul (ϖ ^ n) a
    have e1 : ((normIntegerUnits K L hu.unit : 𝒪[K]ˣ) : 𝒪[K]) =
        1 + ϖ ^ n * Algebra.trace 𝒪[K] 𝒪[L] a + (ϖ ^ n) ^ 2 * d := by
      rw [coe_normIntegerUnits_eq, IsUnit.unit_spec, ← hd, Algebra.smul_def, map_pow]
    have e2 : c - Algebra.trace 𝒪[K] 𝒪[L] a ∈ 𝓂[K] := by
      rw [← residue_eq_zero_iff, map_sub, residue_trace, ht, sub_self]
    obtain ⟨e, he⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp e2
    have hh' : (h : 𝒪[K]) = 1 + ϖ ^ n * c := by
      rw [← hc]
      ring
    rw [mem_maximalIdeal_pow_iff hϖ]
    refine ⟨e - ϖ ^ (n - 1) * d, ?_⟩
    rw [e1, hh']
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    linear_combination (ϖ ^ (m + 1)) * he

theorem map_normIntegerUnits_unitFiltration (n : ℕ) :
    (unitFiltration L n).map (normIntegerUnits K L) = unitFiltration K n :=
  map_eq_of_graded_surjective (unitFiltration_antitone L) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
    (normIntegerUnits K L) (φ := id) tendsto_id n
    (fun _ _ _ hg ↦ normIntegerUnits_mem_unitFiltration hg)
    (fun m _ h hh ↦ by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨g, hg⟩ := exists_normIntegerUnits_div_mem_one (L := L) h
        exact ⟨g, by simp, hg⟩
      · exact exists_normIntegerUnits_div_mem_succ hm hh)

theorem normIntegerUnits_surjective : Function.Surjective (normIntegerUnits K L) := by
  intro h
  have e := map_normIntegerUnits_unitFiltration (K := K) (L := L) 0
  rw [unitFiltration_zero, unitFiltration_zero] at e
  have hh : h ∈ (⊤ : Subgroup 𝒪[L]ˣ).map (normIntegerUnits K L) := by
    rw [e]
    exact Subgroup.mem_top h
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

end Residue

section NormGroup



variable [IsUnramified K L]

theorem mem_range_normUnits_iff (x : Kˣ) :
    x ∈ (normUnits K L).range ↔ (Module.finrank K L : ℤ) ∣ ord (x : K) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [coe_normUnits, ord_norm, IsUnramified.residueDegree_eq_finrank K L]
    exact dvd_mul_right _ _
  · rintro ⟨k, hk⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨⟨m, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 x
    have hm : m.toAdd = Module.finrank K L * k := by
      rw [← hk, ← hx, ord_unitsOfIntProd]
    obtain ⟨v, hv⟩ := normIntegerUnits_surjective (K := K) (L := L) u
    refine ⟨Units.map (algebraMap K L : K →* L) (uniformizerUnit hϖ) ^ k * unitsIncl L v, ?_⟩
    have hnv : normUnits K L (unitsIncl L v) = unitsIncl K (normIntegerUnits K L v) := by
      ext
      rw [coe_normUnits]
      change Algebra.norm K ((v : 𝒪[L]) : L) = _
      rw [← coe_norm_integer (K := K) (L := L) (v : 𝒪[L])]
      exact congrArg (algebraMap 𝒪[K] K) (coe_normIntegerUnits_eq v)
    rw [← hx, unitsOfIntProd_eq, map_mul, map_zpow, hnv, hv, hm, zpow_mul]
    congr 2
    ext
    simp [Algebra.norm_algebraMap]


end NormGroup

end GroundTheory.LocalField
end
end

