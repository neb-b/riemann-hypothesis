module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsExamples

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type w) [Field L] [NumberField L] [Algebra K L]
    (M : HermitianBundle.{v} K), (M.baseChange L).deg = M.deg

section Witnesses

variable (K : Type u) [Field K] [NumberField K]

def doubled : Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  LinearMap.range ((2 : 𝓞 K) • LinearMap.id)

theorem Sublattice.witness :
    Module.finrank (𝓞 K) (doubled K) =
      Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  LinearMap.finrank_range_of_inj (by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    exact smul_right_injective (Fin 2 → 𝓞 K) (two_ne_zero (α := 𝓞 K)) hxy)

theorem LatticeOfLocalisations.witness :
    (∀ v, IsLocalLattice v (localLattice v (FullLattice.standard K 2).carrier)) ∧
      {v : HeightOneSpectrum (𝓞 K) | localLattice v (FullLattice.standard K 2).carrier ≠
        localLattice v (FullLattice.standard K 2).carrier}.Finite :=
  ⟨fun v ↦ localLattice_isLocalLattice v _, Set.finite_empty.subset fun _ hv ↦ hv rfl⟩

theorem LocalChange.witness (v₀ : HeightOneSpectrum (𝓞 K)) :
    {v | swapAt v₀ v ≠ 1}.Finite ∧
      ∀ v, (localLattice v (FullLattice.standard K 2).carrier : Set _) =
        swapAt v₀ v '' localLattice v (FullLattice.standard K 2).carrier :=
  ⟨swapAt_finite v₀, localLattice_swapAt v₀⟩


variable {K} in
theorem norm_scale {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) (σ : K →+* ℂ)
    (x : Fibre σ E) :
    ‖FibreSpace.equiv (h.scale c hc) σ x‖ = c * ‖FibreSpace.equiv h σ x‖ := by
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv (h.scale c hc) σ x)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv h σ x)
  have h3 : ‖FibreSpace.equiv (h.scale c hc) σ x‖ ^ 2 = (c * ‖FibreSpace.equiv h σ x‖) ^ 2 := by
    rw [h1, mul_pow, h2]
    exact Complex.re_ofReal_mul _ _
  rw [← Real.sqrt_sq (norm_nonneg (FibreSpace.equiv (h.scale c hc) σ x)), h3,
    Real.sqrt_sq (by positivity)]

theorem NormComparison.witness (σ : K →+* ℂ) (x : Fibre σ (HermitianBundle.standard K 2).carrier) :
    ‖FibreSpace.equiv ((HermitianBundle.standard K 2).metric.scale 2 two_pos) σ x‖ ≤
      2 * ‖FibreSpace.equiv (HermitianBundle.standard K 2).metric σ x‖ :=
  (norm_scale _ 2 two_pos σ x).le

theorem DiagonalChange.witness :
    (∀ (σ : K →+* ℂ) (x : Fibre σ (HermitianBundle.standard K 2).carrier),
      ‖FibreSpace.equiv ((HermitianBundle.standard K 2).metric.scale 2 two_pos) σ x‖ =
        ‖FibreSpace.equiv (HermitianBundle.standard K 2).metric σ
          (((2 : ℂ) • LinearMap.id : Fibre σ (HermitianBundle.standard K 2).carrier →ₗ[ℂ] _) x)‖) ∧
    ∀ σ : K →+* ℂ, ∃ (n : ℕ)
      (b : OrthonormalBasis (Fin n) ℂ (FibreSpace (HermitianBundle.standard K 2).metric σ))
      (d : Fin n → ℂ), ∀ i, FibreSpace.equiv (HermitianBundle.standard K 2).metric σ
        (((2 : ℂ) • LinearMap.id : Fibre σ (HermitianBundle.standard K 2).carrier →ₗ[ℂ] _)
          ((FibreSpace.equiv (HermitianBundle.standard K 2).metric σ).symm (b i))) = d i • b i := by
  refine ⟨fun σ x ↦ ?_, fun σ ↦ ⟨_, stdOrthonormalBasis ℂ _, fun _ ↦ 2, fun i ↦ ?_⟩⟩
  · rw [norm_scale, LinearMap.smul_apply, LinearMap.id_apply, map_smul, norm_smul,
      Complex.norm_two]
  · rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]

theorem ExactSequence.witness : (HermitianBundle.standard K 2).Saturated (standardFlag K 1) :=
  standardFlag_saturated 1

def flagChain : Fin 3 → Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  fun i ↦ standardFlag K i.rev

theorem ChainSum.witness :
    flagChain K 0 = ⊤ ∧ Antitone (flagChain K) ∧
      ∀ a, (HermitianBundle.standard K 2).Saturated (flagChain K a) :=
  ⟨rfl, fun _ _ hij ↦ standardFlag_monotone (Fin.rev_le_rev.mpr hij),
    fun _ ↦ standardFlag_saturated _⟩

def stdVec : Fin 2 → (HermitianBundle.standard K 2).carrier := fun i ↦ Pi.single i 1

theorem stdVec_eq : stdVec K = ⇑(Pi.basisFun (𝓞 K) (Fin 2)) :=
  funext fun i ↦ (Pi.basisFun_apply (𝓞 K) (Fin 2) i).symm

theorem stdVec_linearIndependent : LinearIndependent (𝓞 K) (stdVec K) := by
  rw [stdVec_eq]
  exact (Pi.basisFun (𝓞 K) (Fin 2)).linearIndependent

theorem stdVec_card :
    Fintype.card (Fin 2) = Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier := by
  rw [Fintype.card_fin]
  exact (Module.finrank_fin_fun (𝓞 K)).symm

theorem stdVec_span :
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
      Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier := by
  rw [finrank_span_eq_card (stdVec_linearIndependent K)]
  exact stdVec_card K

theorem normAt_stdVec (σ : K →+* ℂ) (i : Fin 2) :
    (HermitianBundle.standard K 2).normAt σ (stdVec K i) = 1 := by
  have h := norm_fibreVec_sq (HermitianMetric.standard K (Fin 2)) σ (Pi.single i 1)
  rw [HermitianMetric.standard_inner_single, Complex.one_re] at h
  rw [HermitianBundle.normAt, ← Real.sqrt_sq (norm_nonneg _)]
  exact (congrArg Real.sqrt h).trans Real.sqrt_one

theorem Hadamard.witness :
    LinearIndependent (𝓞 K) (stdVec K) ∧
      Fintype.card (Fin 2) = Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier ∧
        ∀ i (σ : K →+* ℂ), (HermitianBundle.standard K 2).normAt σ (stdVec K i) ≤ 1 :=
  ⟨stdVec_linearIndependent K, stdVec_card K, fun i σ ↦ (normAt_stdVec K σ i).le⟩

theorem HadamardQuotient.witness :
    (HermitianBundle.standard K 2).Saturated (standardFlag K 1) ∧
      Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
        Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier ∧
        ∀ i (σ : K →+* ℂ), (HermitianBundle.standard K 2).normAt σ (stdVec K i) ≤ 1 :=
  ⟨standardFlag_saturated 1, stdVec_span K, fun i σ ↦ (normAt_stdVec K σ i).le⟩

theorem HadamardMean.witness :
    LinearIndependent (𝓞 K) (stdVec K) ∧
      Fintype.card (Fin 2) = Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  ⟨stdVec_linearIndependent K, stdVec_card K⟩

theorem HadamardMeanQuotient.witness :
    (HermitianBundle.standard K 2).Saturated (standardFlag K 1) ∧
      Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
        Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  ⟨standardFlag_saturated 1, stdVec_span K⟩

end Witnesses

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
