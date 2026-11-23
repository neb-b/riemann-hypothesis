module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0032
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeVdLeOne
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem κι_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  intro h
  apply ha
  have h1 : ι a = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [h1, map_zero])

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

section Line

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit hK hF in
theorem h_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  ring

end Line

theorem exists_norm_congr_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ∉ 𝔭) {k : ℕ}
    (hk : 1 ≤ k) : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 k le_rfl hk (ι c) (idealPowerSpanBounds.conjO_map hF c) hcP
  by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have h3 := h1 hc'
    have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hpos : (0 : ℝ) < (normRepCount K (P ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos hs _) ?_
      have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hc']
    exact hα
  · have h3 := h2 hc'
    have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos (by linarith) _) ?_
      have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
        rw [Nat.cast_one, zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ hN
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.extP_split hK hF hP hc']
    exact hα

end Formalism.L2.SG.Pf.TemperedBoundGL3
