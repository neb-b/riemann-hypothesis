module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField Matrix
open scoped ComplexOrder

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {φ | ∀ v ∈ L, φ ⬝ᵥ v ∈ Set.range (algebraMap (𝓞 K) K)}
  add_mem' := by
    intro φ ψ hφ hψ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    obtain ⟨b, hb⟩ := hψ v hv
    exact ⟨a + b, by rw [map_add (f := _), ha, hb, add_dotProduct]⟩
  zero_mem' := fun v _ ↦ ⟨0, by rw [map_zero, zero_dotProduct]⟩
  smul_mem' := by
    intro c φ hφ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    exact ⟨c * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩

structure IsDualBasis {m N : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (φ : Fin (N + 1) → Fin m → K) : Prop where
  independent : LinearIndependent ℤ φ
  span_eq : Submodule.span ℤ (Set.range φ) = (latticeDual L).restrictScalars ℤ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem prod_zpow_single {M : Type*} [CommGroupWithZero M] (f : ι → M) (k₀ : ι) :
    ∏ k, f k ^ ((Pi.single k₀ 1 : ι → ℤ) k) = f k₀ := by
  rw [Finset.prod_eq_single k₀ (fun k _ hk ↦ by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h ↦ absurd (Finset.mem_univ k₀) h), Pi.single_eq_same, zpow_one]

omit [Fintype ι] in
theorem single_cast (k₀ k : ι) : (((Pi.single k₀ 1 : ι → ℕ) k : ℕ) : ℤ) = (Pi.single k₀ 1 : ι → ℤ) k := by
  by_cases h : k = k₀
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

namespace ArithVariety

variable (n : ι → ℕ)


omit [Fintype ι] in
theorem whole_mkF_X_ne_zero (v : Coord n) : (whole (n := n)).mkF (X v) ≠ 0 := fun h ↦
  X_ne_zero v (Ideal.mem_bot.mp (((whole (n := n)).mkF_eq_zero_iff _).mp h))



end ArithVariety

variable (n : ι → ℕ) (k₀ : ι)

def blockAddData : AddBlockData (ArithVariety.whole (n := n)) where
  deg := Pi.single k₀ 1
  size := n k₀
  elt j := (ArithVariety.whole (n := n)).mkF (X ⟨k₀, j⟩)
  elt_deg j := ⟨X ⟨k₀, j⟩, 1, (Pi.single k₀ 1 : ι → ℕ), 0, isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩,
    isWeightedHomogeneous_one ℤ (coordDeg n), fun k ↦ by simp [single_cast],
    (Ideal.ne_top_iff_one _).mp (ArithVariety.whole (n := n)).isPrime.ne_top,
    by rw [map_one, div_one]⟩
  chart_mem c _ j := by
    rw [ArithVariety.chartPow, prod_zpow_single]
    exact Subring.subset_closure ⟨⟨k₀, j⟩, rfl⟩
  generating c _ := by
    refine ⟨Pi.single (c k₀) 1, fun j ↦ ?_, ?_⟩
    · by_cases h : j = c k₀
      · subst h; rw [Pi.single_eq_same]; exact Subring.one_mem _
      · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _
    · rw [Finset.sum_eq_single (c k₀) (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h ↦ absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
        ArithVariety.chartPow, prod_zpow_single]
      exact div_self (ArithVariety.whole_mkF_X_ne_zero n _)

def blockForms : ((k : ι) → Fin (n k + 1)) → Fin ((blockAddData n k₀).size + 1) →
    MvPolynomial (Coord n) ℤ :=
  fun c j ↦ chartMonomial c 1 * X ⟨k₀, j⟩

def blockLine : HermLine n where
  deg := Pi.single k₀ 1
  metric z := l2Norm (z k₀)
  metric_pos z hz := vectorL2Norm_pos (hz k₀)
  metric_smul c z _ _ := by
    rw [vectorL2Norm_const_mul, prod_zpow_single (fun k ↦ ‖c k‖) k₀]
  metric_smooth := contDiffOn_l2Norm_block k₀

def blockVal : Coord (blockAddData n k₀).extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => X ⟨k₀, j⟩
  | ⟨some k, i⟩ => X ⟨k, i⟩

def blockSubst :
    MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ →+* MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (blockVal n k₀ v) * X v.1





end

end GroundTheory.Heights₂.Heights
end

