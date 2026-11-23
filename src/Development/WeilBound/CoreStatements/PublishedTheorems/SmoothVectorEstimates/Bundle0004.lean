module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AdelicCharacterCondition
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AdelicCharacterCondition

theorem isCharAF_of {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF E ψ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  have hb : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime, hb⟩
  exact ⟨hψ.cont, hψ.norm, hψ.rat, _, hy⟩

theorem condAA {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    ∀ᶠ v in (cofinite : Filter (HeightOneSpectrum (𝓞 E))), ∀ t : v.adicCompletion E,
      (∀ s ∈ v.adicCompletionIntegers E, ψ (sFin E (sLoc E v (s * t))) = 1) ↔ t ∈ v.adicCompletionIntegers E := by
  have h := _root_.PI.VolStabSW.VolAAW.condAA_of (_root_.PI.VolStabSW.VolAAW.condExact_of _root_.PI.VolStabSW.sAf_holds
    (_root_.PI.VolStabSW.chInf_of_lift _root_.PI.VolStabSW.chLift_holds)) E ψ (isCharAF_of hψ)
  filter_upwards [h] with v hv t
  simp only [sFin_sLoc_eq]
  exact hv t

end AdelicCharacterCondition

theorem adelic_character_holds : StandardCharacterExists := by
  intro E _ _ _
  obtain ⟨ψ, hψ⟩ := exists_stdPsi E
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [AdelicCharacterCondition.condAA hψ] with w hw
  have hint : ∀ y ∈ Ov E w, ψ (sFin E (sLoc E w y)) = 1 := by
    intro y hy
    have := (hw 1).2 (one_mem _) y hy
    rwa [mul_one] at this
  refine ⟨hint, ?_⟩
  set ϖ := _root_.PI.VolStabSW.unifV w with hϖ
  have hϖ0 : ϖ ≠ 0 := (_root_.PI.VolStabSW.unifV_spec w).1
  have hu : IsUnifV E w ϖ := _root_.PI.VolStabSW.unifV_val w
  have hnot : ϖ⁻¹ ∉ w.adicCompletionIntegers E := by
    intro h
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := _root_.PI.VolStabSW.unifV_val w
    rw [hv] at h
    exact absurd h (by decide)
  have hex : ¬ ∀ s ∈ w.adicCompletionIntegers E, ψ (sFin E (sLoc E w (s * ϖ⁻¹))) = 1 :=
    fun h => hnot ((hw _).1 h)
  push Not at hex
  obtain ⟨s, hs, hne⟩ := hex
  refine ⟨ϖ, s * ϖ⁻¹, hu, ?_, hne⟩
  rw [mul_comm s, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  exact hs

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AveragingProjection
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AveragingProjection

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem avg_add (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    avg Γ (fun x => Φ x + Ψ x) = avg Γ Φ + avg Γ Ψ := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [h.choose_spec.2.2]; exact ENNReal.one_ne_top)
    exact integral_add (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))
  · simp

theorem avg_zero (Γ : AddSubgroup G) : avg Γ (fun _ => (0 : ℂ)) = 0 := by
  simpa using avg_const_mul Γ 0 (fun _ => (0 : ℂ))

theorem norm_avg_sub_le (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) {C : ℝ} (hC : 0 ≤ C) (hd : ∀ x, ‖Φ x - Ψ x‖ ≤ C) :
    ‖avg Γ Φ - avg Γ Ψ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have e1 : h.choose.1 h.choose.2 = 1 := h.choose_spec.2.2
    have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [e1]; exact ENNReal.one_ne_top)
    rw [← integral_sub (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))]
    calc _ ≤ C * h.choose.1.real h.choose.2 :=
          norm_setIntegral_le_of_norm_le_const (by rw [e1]; exact ENNReal.one_lt_top) fun x _ => hd x
      _ = C := by simp [Measure.real, e1]
  · simpa using hC

theorem continuous_avg {X : Type} [TopologicalSpace X] (Γ : AddSubgroup G) {u : G → X} (hu : Continuous u) :
    Continuous fun φ : X →ᵇ ℂ => avg Γ (fun x => φ (u x)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun φ ψ => ?_).continuous
  rw [dist_eq_norm, NNReal.coe_one, one_mul]
  exact norm_avg_sub_le Γ (φ.continuous.comp hu) (ψ.continuous.comp hu) (B := max ‖φ‖ ‖ψ‖)
    (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
    (fun x => (ψ.norm_coe_le_norm _).trans (le_max_right _ _)) dist_nonneg
    (fun x => by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist (f := φ) (g := ψ) (u x))

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

def P (ψ : AddChar (Ad E) ℂ) (φ : XB E a) : Prop :=
  Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g

theorem P_zero : P ψ (0 : XB E a) := by
  refine ⟨⟨(0 : XB E a).continuous, fun γ _ g => rfl, fun k _ y g => by simp, fun r _ _ g => ?_⟩, fun γ g => rfl⟩
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  exact avg_zero _

theorem P_add {φ φ' : XB E a} (h : P ψ φ) (h' : P ψ φ') : P ψ (φ + φ') := by
  refine ⟨⟨(φ + φ').continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.left γ hγ g, h'.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.law k hk y g, h'.1.law k hk y g, mul_add]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [avg_add _ (Φ := fun x => φ (blkU x * g)) (Ψ := fun x => φ' (blkU x * g)) (φ.continuous.comp ((continuous_posU _).mul continuous_const))
      (φ'.continuous.comp ((continuous_posU _).mul continuous_const)) (B := max ‖φ‖ ‖φ'‖)
      (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
      (fun x => (φ'.norm_coe_le_norm _).trans (le_max_right _ _)),
      h.1.van r hr hr' g, h'.1.van r hr hr' g, add_zero]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.2 γ g, h'.2 γ g]

theorem P_smul (c : ℂ) {φ : XB E a} (h : P ψ φ) : P ψ (c • φ) := by
  refine ⟨⟨(c • φ).continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, h.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, h.1.law k hk y g]
    ring
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [avg_const_mul, h.1.van r hr hr' g, mul_zero]
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, h.2 γ g]

theorem P_rt (k : GA E a) {φ : XB E a} (h : P ψ φ) : P ψ (Rt E a k φ) := by
  refine ⟨⟨(Rt E a k φ).continuous, fun γ hγ g => ?_, fun j hj y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [Rt_apply, mul_assoc]; exact h.1.left γ hγ (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.law j hj y (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.van r hr hr' (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.2 γ (g * k)

theorem isClosed_P : IsClosed {φ : XB E a | P ψ φ} := by
  have key : {φ : XB E a | P ψ φ} =
      (⋂ (γ : GL (Fin a) E), ⋂ (g : GA E a), {φ : XB E a | φ (ratGL E a γ * g) = φ g}) ∩
      ((⋂ (k : ℕ), ⋂ (_ : a - 1 < k), ⋂ (y : UnipotentBlockColumnIndex a k k → Ad E), ⋂ (g : GA E a),
          {φ : XB E a | φ (blkU y * g) = ψ (dot (eLast a k) y) * φ g}) ∩
        (⋂ (r : ℕ), ⋂ (_ : 0 < r), ⋂ (_ : r ≤ a - 1), ⋂ (g : GA E a),
          {φ : XB E a | avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => φ (blkU x * g)) = 0})) := by
    ext φ
    simp only [P, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hG, hl⟩
      exact ⟨hl, hG.law, hG.van⟩
    · rintro ⟨hl, hlaw, hvan⟩
      exact ⟨⟨φ.continuous, fun γ _ g => hl γ g, hlaw, hvan⟩, hl⟩
  rw [key]
  refine (isClosed_iInter fun γ => isClosed_iInter fun g => ?_).inter
    ((isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun y => isClosed_iInter fun g => ?_).inter
      (isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun g => ?_))
  · exact isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
  · exact isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const _))
  · exact isClosed_eq (continuous_avg _ ((continuous_posU _).mul continuous_const)) continuous_const

end AveragingProjection

open AveragingProjection in
theorem averaging_projection_linear : G2a := by
  intro E _ _ _ a ψ _
  refine ⟨{ carrier := {φ | P ψ φ}, add_mem' := P_add, zero_mem' := P_zero, smul_mem' := P_smul },
    isClosed_P, fun g φ h => P_rt g h, fun φ => Iff.rfl⟩

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BoundedInvariantL2
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace BoundedInvariantL2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem memL2Quotient_of_bounded_left_invariant [IsFiniteMeasure (quotMeasure Γ μ)] (φ : G →ᵇ ℂ) (h : LeftInv Γ φ) : MemL2Quotient Γ μ φ := by
  refine ⟨h, MemLp.of_bound ?_ ‖φ‖ (Eventually.of_forall fun q => φ.norm_coe_le_norm q.out)⟩
  rw [aestronglyMeasurable_quotMeasure_iff_lift, h.lift_descend]
  exact φ.continuous.aestronglyMeasurable

theorem norm_toL2_sub_le_sup_norm [IsFiniteMeasure (quotMeasure Γ μ)] (φ ψ : G →ᵇ ℂ) (hφ : MemL2Quotient Γ μ φ)
    (hψ : MemL2Quotient Γ μ ψ) :
    ‖hφ.toL2 - hψ.toL2‖ ≤ (measureUnivNNReal (quotMeasure Γ μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹ * ‖φ - ψ‖ := by
  have hd : LeftInv Γ ⇑(φ - ψ) := fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g]
  have h := memL2Quotient_of_bounded_left_invariant (μ := μ) (φ - ψ) hd
  have e : hφ.toL2 - hψ.toL2 = h.toL2 := (MemLp.toLp_sub hφ.2 hψ.2).symm
  rw [e]
  exact Lp.norm_le_of_ae_bound (norm_nonneg _)
    (h.coeFn_toL2.mono fun q hq => by rw [hq]; exact (φ - ψ).norm_coe_le_norm _)

end BoundedInvariantL2

theorem bounded_invariant_functions_in_L2 : G2b := by
  intro E _ _ _ a μ _ _ H hH
  have := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  let Y : Submodule ℂ (XB E a) :=
    { carrier := {φ | ∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H}
      add_mem' := by
        rintro φ ψ ⟨h1, m1⟩ ⟨h2, m2⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(φ + ψ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g, h2.1 γ hγ g], h1.2.add h2.2⟩
        have e : h.toL2 = h1.toL2 + h2.toL2 := MemLp.toLp_add h1.2 h2.2
        exact ⟨h, e ▸ H.add_mem m1 m2⟩
      zero_mem' := by
        have h : MemL2Quotient (latticeGL E a) μ ⇑(0 : XB E a) := ⟨fun γ hγ g => rfl, MemLp.zero⟩
        have e : h.toL2 = 0 := MemLp.toLp_zero h.2
        exact ⟨h, e ▸ H.zero_mem⟩
      smul_mem' := by
        rintro c φ ⟨h1, m1⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(c • φ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g], h1.2.const_smul c⟩
        have e : h.toL2 = c • h1.toL2 := MemLp.toLp_const_smul c h1.2
        exact ⟨h, e ▸ H.smul_mem c m1⟩ }
  refine ⟨Y, ?_, ?_, fun φ => Iff.rfl⟩
  · refine IsSeqClosed.isClosed fun {x p} hx hp => ?_
    choose hxm hxH using hx
    have hpl : LeftInv (latticeGL E a) ⇑p := fun γ hγ g => by
      have t1 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p (γ * g))) :=
        ((continuous_eval_const (γ * g)).tendsto p).comp hp
      have t2 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p g)) := by
        have := ((continuous_eval_const g).tendsto p).comp hp
        refine this.congr fun n => ?_
        exact ((hxm n).1 γ hγ g).symm
      exact tendsto_nhds_unique (f := fun n => x n (γ * g)) (l := (atTop : Filter ℕ)) t1 t2
    have hp2 := BoundedInvariantL2.memL2Quotient_of_bounded_left_invariant (μ := μ) p hpl
    refine ⟨hp2, hH.1.mem_of_tendsto (f := fun n => (hxm n).toL2) (b := (atTop : Filter ℕ)) ?_
      (Eventually.of_forall hxH)⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hn : Tendsto (fun n => ‖x n - p‖) atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hp
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => BoundedInvariantL2.norm_toL2_sub_le_sup_norm (x n) p (hxm n) hp2) ?_
    simpa using hn.const_mul ((measureUnivNNReal (quotMeasure (latticeGL E a) μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹)
  · rintro g φ ⟨h, m⟩
    have m' := hH.2 g _ m
    rw [right_translate_toL2] at m'
    exact ⟨h.mul_right g, m'⟩

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CharacterNondegenerate
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CharacterNondegenerate

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ := ψ.compAddMonoidHom (sInf E).toAddMonoidHom

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chi ψ z = ψ (sInf E z) := rfl

theorem pInf_sInf (z : Cinf E) : pInf E (sInf E z) = z := (infEq E).symm_apply_apply z

theorem pFin_sInf (z : Cinf E) : pFin E (sInf E z) = 0 := rfl

theorem sInf_mul (z : Cinf E) (x : Ad E) : sInf E z * x = sInf E (z * pInf E x) := by
  refine ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

theorem continuous_chi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Continuous (chi ψ) :=
  hψ.cont.comp continuous_sInf

theorem chi_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E) (hz : ∀ w, chi ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by rw [sInf_mul]; exact hz _
  have hd0 : d = 0 := by
    by_contra h0
    obtain ⟨w⟩ := nonempty_pl (E := E)
    have h1 : sInf E z * algebraMap E (Ad E) d⁻¹ = 1 := by
      rw [hd, ← map_mul, mul_inv_cancel₀ h0, map_one]
    have h2 := congrArg (fun x => pLoc E w (pFin E x)) h1
    simp only [map_mul, pFin_sInf, zero_mul, map_zero, map_one] at h2
    exact zero_ne_one h2
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

theorem sInf_lastE (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Cinf E) :
    sInf E (lastE k y) = lastE k (fun t => sInf E (y t)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lastE, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem polyBd : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
  show ‖Rt E a (infGL E a g) x‖ ≤ 1 * _ ^ 0 * ‖x‖
  rw [pow_zero, mul_one, one_mul, norm_Rt]⟩

end CharacterNondegenerate

open CharacterNondegenerate in
theorem whittaker_nondegenerate_character : S7 → MirabolicColumnBlock → G0 → G5 → G6 := by
  intro hS7 hS10 hG0 hG5 E _ _ _ a ψ hψ S Y Y' hY hY' n m hn hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', hW1, hWeq⟩ := hSt
  obtain ⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -⟩ := hG0 E a
  obtain ⟨hΛ, hRt, hGood, hlaw⟩ := hG5 E a ψ hψ
  obtain ⟨hdec, -, -, hBlk1, -⟩ := hS10 (Cinf E) a (n + 1)
  obtain ⟨η, r, hη1, hr1, hmir, -, -, hv⟩ := hS7 (InfinitePlace E) a (XB E a) (repI E a) polyBd n hn (chi ψ)
    (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) Set.univ Filter.univ_mem
  have memY : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g, ∀ x ∈ Z, repI E a g x ∈ Z :=
    fun Z hZ g x hx => hZ.stable _ (fun w _ => hcLI w g) x hx
  have whB : ∀ x : XB E a, Good ψ (a - 1) x → ∀ (y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E) (g : GA E a),
      Wh ψ x (infGL E a (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ x g := by
    intro x hx y g
    rw [hb, chi_apply, sInf_lastE]
    exact (hlaw x hx).2.2 (n + 1) n.succ_pos _ g
  have lawOf : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g' : GA E a, cInf g' = 1 →
      ∀ Λ : XB E a →L[ℂ] ℂ, (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x ∈ Z, ∀ y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E,
        Λ (repI E a (blkU y) x) = chi ψ (lastE (n + 1) y) * Λ x := by
    intro Z hZ g' hg' Λ hΛg x hx y
    have hx' := hZ.good x hx
    change Λ (Rt E a (infGL E a (blkU y)) x) = _
    rw [hΛg _ (hGood x _ hx'), hΛg x hx', hRt, hcomm g' hg', whB x hx']
  have levOf : ∀ x x' : XB E a, Lev S x → (∀ Z : Submodule ℂ (XB E a), IsClosed (Z : Set (XB E a)) →
      (∀ g, ∀ y ∈ Z, repI E a g y ∈ Z) → x ∈ Z → x' ∈ Z) → Lev S x' := by
    intro x x' hx hZ w hw
    refine Filter.mem_of_superset (hx w hw) fun u hu => ?_
    have hu' : Rt E a (fl a w u) x = x := hu
    let T : XB E a →L[ℂ] XB E a := Rt E a (fl a w u) - ContinuousLinearMap.id ℂ _
    have hmem : ∀ y, T y = 0 ↔ Rt E a (fl a w u) y = y := fun y => by simp [T, sub_eq_zero]
    have hk := hZ _ T.isClosed_ker (fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        refine (hmem _).2 ?_
        have hy' := (hmem y).1 hy
        change Rt E a (fl a w u) (Rt E a (infGL E a g) y) = Rt E a (infGL E a g) y
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul,
          ContinuousLinearMap.mul_apply, hy'])
      (LinearMap.mem_ker.2 ((hmem x).2 hu'))
    rw [LinearMap.mem_ker] at hk
    exact (hmem x').1 hk
  obtain ⟨v, hvs, hvP⟩ := hv φ hsm
  obtain ⟨v', hvs', hvP'⟩ := hv φ' hsm'
  obtain ⟨hvY, hvΛ⟩ := hvP Y hY.closed (memY Y hY) hφY
  obtain ⟨hvY', hvΛ'⟩ := hvP' Y' hY'.closed (memY Y' hY') hφY'
  have conv : ∀ (g' : GA E a) (Λ : XB E a →L[ℂ] ℂ), (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x : XB E a, Good ψ (a - 1) x → ∀ k, Λ (repI E a k x) = Wh ψ x (g' * infGL E a k) := by
    intro g' Λ hΛg x hx k
    change Λ (Rt E a (infGL E a k) x) = _
    rw [hΛg _ (hGood x _ hx), hRt]
  have hgY := hY.good
  have hgY' := hY'.good
  refine ⟨v, hvY, v', hvY', hvs, hvs', levOf φ v hlev fun Z hc hs hx => (hvP Z hc hs hx).1,
    levOf φ' v' hlev' fun Z hc hs hx => (hvP' Z hc hs hx).1, ?_, ?_⟩
  · obtain ⟨Λ₁, hΛ₁⟩ := hΛ 1
    have e1 := hvΛ Λ₁ (lawOf Y hY 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1
    rw [conv 1 Λ₁ hΛ₁ v (hgY v hvY), conv 1 Λ₁ hΛ₁ φ (hgY φ hφY), hr1, map_one, one_mul] at e1
    rw [e1]
    exact mul_ne_zero hη1 hW1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    obtain ⟨y, h, hh, hyh⟩ := hdec (cInf g) hgI
    obtain ⟨g', hg'⟩ : ∃ g' : GA E a, g' = (infGL E a (cInf g))⁻¹ * g := ⟨_, rfl⟩
    have hg'1 : cInf g' = 1 := by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]
    have hgeq : g = infGL E a (blkU y) * (g' * infGL E a h) := by
      rw [hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]
    obtain ⟨Λ, hΛg⟩ := hΛ g'
    have e := hvΛ Λ (lawOf Y hY g' hg'1 Λ hΛg) h hh
    have e' := hvΛ' Λ (lawOf Y' hY' g' hg'1 Λ hΛg) h hh
    rw [conv g' Λ hΛg v (hgY v hvY), conv g' Λ hΛg φ (hgY φ hφY)] at e
    rw [conv g' Λ hΛg v' (hgY' v' hvY'), conv g' Λ hΛg φ' (hgY' φ' hφY')] at e'
    rw [hgeq, whB v (hgY v hvY), whB v' (hgY' v' hvY'), e, e']
    by_cases hη : η h = 0
    · simp [hη]
    · rw [hWeq _ ⟨?_, fun w => ?_⟩]
      · rw [map_mul, hg'1, one_mul, hcI]
        exact hmir h hh hη
      · rw [map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]
        exact hgL w

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PSmoNorm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

theorem smonorm_of : Meet → CuspidalIrreducibleSubrep → SmoNorm := by
  intro hM hG E _ _ _ a π π' hπ hπ' hS
  let μ : Measure (GA E a) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨H, hH, hf⟩ := hG E a μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E a μ π' hπ'
  have hne : H ⊓ H' ≠ ⊥ := hM E a μ π π' H H' hπ hπ' hH.1 hH'.1
    (fun φ hφ => ⟨hf.finitePartMemL2 φ hφ, hf.classes_le (toL2_mem_classes hφ (hf.finitePartMemL2 φ hφ))⟩)
    (fun φ hφ => ⟨hf'.finitePartMemL2 φ hφ, hf'.classes_le (toL2_mem_classes hφ (hf'.finitePartMemL2 φ hφ))⟩) hS
  have h1 : H ⊓ H' = H := (hH.2.2 _ inf_le_left (hH.1.inf hH'.1)).resolve_left hne
  have h2 : H ⊓ H' = H' := (hH'.2.2 _ inf_le_right (hH.1.inf hH'.1)).resolve_left hne
  have e : H = H' := h1.symm.trans h2
  subst e
  exact hf.unique hf'

end PositivityTheory.jumpWindows

end
end

