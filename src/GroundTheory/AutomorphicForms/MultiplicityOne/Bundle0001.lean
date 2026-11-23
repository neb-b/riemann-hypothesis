module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicDistribution
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
section
open MeasureTheory Measure Topology Filter Set IsDedekindDomain NumberField

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem isMulRightInvariant_finite (μ : Measure (AdelicGLn.FiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.FiniteAdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨fun g => ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [mul_one]
    exact Measure.map_id
  let _ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _
  have : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  set P := μi.prod μ
  set e := AdelicGLn.prodEquiv K n
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  have hν := GJGlobal.isMulRightInvariant_haar ν hn
  have he : Measurable e := e.continuous.measurable
  have : (ν.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map ν e.toMulEquiv e.continuous e.symm.continuous
  have hν' : ∀ p, (ν.map e).map (· * p) = ν.map e := by
    intro p
    have hcomp : (· * p) ∘ e = e ∘ (· * e.symm p) := by
      funext x
      simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
    rw [Measure.map_map (measurable_mul_const p) he, hcomp,
      ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

  set_option synthInstance.maxHeartbeats 400000 in
  set c := haarScalarFactor (ν.map e) P
  have hc : ν.map e = c • P := isMulLeftInvariant_eq_smul (ν.map e) P
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    have hne := isOpen_univ.measure_ne_zero (ν.map e) univ_nonempty
    rw [hc] at hne
    exact hne rfl
  have hP : ∀ p, P.map (· * p) = P := by
    intro p
    have h1 : P = c⁻¹ • ν.map e := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1, Measure.map_smul _ (measurable_mul_const p).aemeasurable, hν']
  refine ⟨fun g => ?_⟩
  have hprod : P.map (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = μi.prod (μ.map (· * g)) := by
    have hf : (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = Prod.map id (· * g) := by
      funext p
      exact Prod.ext (mul_one p.1) rfl
    rw [hf, ← Measure.map_prod_map μi μ measurable_id (measurable_mul_const g), Measure.map_id]
  rw [hP] at hprod
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds (1 : AdelicGLn.InfiniteAdelicGL K n)
  have hA0 : μi A ≠ 0 := (measure_pos_of_mem_nhds μi hA).ne'
  have hAt : μi A ≠ ⊤ := hAc.measure_lt_top.ne
  refine Measure.ext fun B hB => ?_
  have h1 := congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod
  simp only [P, Measure.prod_prod] at h1
  exact ((ENNReal.mul_right_inj hA0 hAt).1 h1).symm

end

end Whittaker

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.MultiplicityOne.NormOne
section
open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def openSubgroupOf (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    OpenSubgroup (AdelicGLn.FiniteAdelicGL K n) where
  toSubgroup := U.map (AdelicGLn.integralFiniteGL K n).subtype
  isOpen' := by
    change IsOpen ((U.map (AdelicGLn.integralFiniteGL K n).subtype : Subgroup _) :
      Set (AdelicGLn.FiniteAdelicGL K n))
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU

def IsSmoothTest (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) : Prop :=
  ∃ (ν : Measure (ArchUnits K n)) (_ : ν.IsHaarMeasure) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (β : ArchMatrix K n → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ),
    f = archConv ν hβ.continuous hβc hβu (finAvg U hU g)

theorem IsSmoothTest.exists_finOne_mul {f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ}
    (hf : IsSmoothTest f) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      ∀ u ∈ U, ∀ x, f (finOne K n u * x) = f x := by
  obtain ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩ := hf
  refine ⟨U, hU, fun u hu x => ?_⟩
  rw [archConv_apply, archConv_apply]
  exact archConvFun_finOne_mul _ _ u (fun y => finAvgFun_finOne_mul U hU g ⟨u, hu⟩ y) x

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

theorem exists_isSmoothTest_near (g : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ,
      IsSmoothTest f ∧ ∫ x, ‖g x - f x‖ ∂μ ≤ ε := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ArchUnits K n), ν.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  obtain ⟨U, hU, β, hβ, hβc, hβu, -, hclose⟩ := exists_smooth_approx μ ν g hε
  exact ⟨_, ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩,
    le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)) hclose⟩

theorem _root_.GroundTheory.Automorphic.UnitaryRep.integrated_eq_zero_of_dense {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (P : CompactlySupportedContinuousMap G ℂ → Prop)
    (hP : ∀ (g : CompactlySupportedContinuousMap G ℂ) (ε : ℝ), 0 < ε →
      ∃ f, P f ∧ ∫ x, ‖g x - f x‖ ∂ν ≤ ε)
    {v : H} (h : ∀ f, P f → π.integrated ν (UnitaryRep.ccToL1 ν f) v = 0)
    (g : CompactlySupportedContinuousMap G ℂ) : π.integrated ν (UnitaryRep.ccToL1 ν g) v = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have hε' : 0 < ε / (‖v‖ + 1) := div_pos hε (by positivity)
  obtain ⟨f, hfs, hclose⟩ := hP g _ hε'
  have hf0 := h f hfs
  have hd := π.dist_integrated_ccToL1_le ν g f
  have hv1 : ‖v‖ / (‖v‖ + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [dist_eq_norm] at hd
  calc ‖π.integrated ν (UnitaryRep.ccToL1 ν g) v‖
      = ‖(π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)) v‖ := by
        rw [sub_apply, hf0, sub_zero]
    _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ v
    _ ≤ (ε / (‖v‖ + 1)) * ‖v‖ := by gcongr; exact hd.trans hclose
    _ = ε * (‖v‖ / (‖v‖ + 1)) := by ring
    _ ≤ ε * 1 := by gcongr
    _ = 0 + ε := by ring

end MultiplicityOne

end

end GroundTheory.Automorphic
end

