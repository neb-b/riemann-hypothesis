module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableSubspaceHasWeightVector
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TorusWtExist

theorem charR_eq_exp (χ : ℝ → ℂ) (hc : Continuous χ) (hm : ∀ s t, χ (s + t) = χ s * χ t)
    (h0 : χ 0 = 1) (h2 : χ (2 * Real.pi) = 1) : ∃ m : ℤ, ∀ t : ℝ, χ t = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ s, |s| ≤ δ → ‖χ s - 1‖ ≤ 1 / 2 := by
    have := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
    obtain ⟨δ, hδ, h⟩ := this
    refine ⟨δ / 2, by positivity, fun s hs => ?_⟩
    have := h s (by rw [Real.dist_eq, sub_zero]; linarith)
    rw [dist_eq_norm, h0] at this
    exact this.le
  set c : ℂ := ∫ s in (0 : ℝ)..δ, χ s with hcdef
  have hint : ∀ a b : ℝ, IntervalIntegrable χ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  have hc0 : c ≠ 0 := by
    intro h
    have h1 : ‖∫ s in (0 : ℝ)..δ, (χ s - 1)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      exact hδc s (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
    rw [intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const, ← hcdef, h] at h1
    simp only [intervalIntegral.integral_const, sub_zero, zero_sub, norm_neg, Complex.real_smul, mul_one] at h1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at h1
    linarith
  set F : ℝ → ℂ := fun u => ∫ s in (0 : ℝ)..u, χ s with hF
  have hFd : ∀ t, HasDerivAt F (χ t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hid : ∀ t, χ t = (F (t + δ) - F t) / c := by
    intro t
    rw [eq_div_iff hc0]
    have h1 : ∫ s in (0 : ℝ)..δ, χ (t + s) = F (t + δ) - F t := by
      rw [intervalIntegral.integral_comp_add_left (fun x => χ x) t, add_zero, hF]
      simp only
      rw [intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)]
    rw [← h1, hcdef, ← intervalIntegral.integral_const_mul]
    congr 1; funext s; rw [hm]
  set a : ℂ := (χ δ - 1) / c with ha
  have hd : ∀ t : ℝ, HasDerivAt χ (χ t * a) t := by
    intro t
    have h1 : HasDerivAt (fun t => (F (t + δ) - F t) / c) ((χ (t + δ) - χ t) / c) t := by
      have := ((hFd (t + δ)).comp_add_const t δ).sub (hFd t)
      exact this.div_const c
    have hfun : χ = fun t => (F (t + δ) - F t) / c := funext hid
    have h3 : (χ (t + δ) - χ t) / c = χ t * a := by rw [hm, ha]; ring
    rw [h3, ← hfun] at h1
    exact h1
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * t)) * χ t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(a * t))) (Complex.exp (-(a * t)) * (-a)) t := by
      have : HasDerivAt (fun t : ℝ => -(a * (t : ℂ))) (-a) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a).fun_neg
      exact this.cexp
    have h2 := h1.mul (hd t)
    have h3 : Complex.exp (-(a * t)) * (-a) * χ t + Complex.exp (-(a * t)) * (χ t * a) = 0 := by ring
    rw [h3] at h2
    exact h2
  have hconst : ∀ t : ℝ, Complex.exp (-(a * t)) * χ t = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
    rw [this]; simp [h0]
  have hexp : ∀ t : ℝ, χ t = Complex.exp (a * t) := by
    intro t
    have h := hconst t
    rw [Complex.exp_neg] at h
    field_simp at h
    exact h
  have h2' := h2
  rw [hexp, Complex.exp_eq_one_iff] at h2'
  obtain ⟨k, hk⟩ := h2'
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hak : a = k * Complex.I := by
    have : a * ((2 * Real.pi : ℝ) : ℂ) = (k * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) := by
      rw [hk]; push_cast; ring
    exact mul_right_cancel₀ hpi this
  refine ⟨k, fun t => ?_⟩
  rw [hexp, hak]; push_cast; ring_nf

def dT {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem dT_mem_Kset {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) : dT θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, dT, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · rw [dT, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem Kset_sub_UJset {n : ℕ} (ε : Fin n → Bool) :
    ∀ g ∈ Formalism.REAL.Kset ε, g ∈ Formalism.MainNotions.S.UJset ε := by
  rintro g ⟨hu, hc⟩
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mem_unitaryGroup_iff'] at hu
  rw [mul_assoc, ← hc, ← mul_assoc, ← Matrix.star_eq_conjTranspose, hu, one_mul]

theorem dT_add {n : ℕ} (θ θ' : Fin n → ℝ) : dT (θ + θ') = dT θ * dT θ' := by
  rw [dT, dT, dT, Matrix.diagonal_mul_diagonal]
  congr 1; funext a
  rw [← Complex.exp_add]; congr 1; simp only [Pi.add_apply]; push_cast; ring

theorem dT_zero {n : ℕ} : dT (0 : Fin n → ℝ) = 1 := by
  rw [dT, ← Matrix.diagonal_one]; congr 1; funext a; simp

theorem dT_two_pi {n : ℕ} (a : Fin n) : dT (Pi.single a (2 * Real.pi)) = 1 := by
  rw [dT, ← Matrix.diagonal_one]; congr 1; funext b
  by_cases h : b = a
  · subst h; simp only [Pi.single_eq_same, Pi.one_apply]
    rw [Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩
  · simp [Pi.single_eq_of_ne h]

theorem continuous_dT {n : ℕ} : Continuous (dT (n := n)) := by
  unfold dT
  apply Continuous.matrix_diagonal
  fun_prop

theorem exists_torus_weight_vector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ →
    (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → S ≠ ⊥ →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ S ∧ v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v := by
  intro n ε H _ _ ρ hrep hcont _ S hfd hstab hne
  classical
  set T : (Fin n → ℝ) → (H →L[ℂ] H) := fun θ => ρ (dT θ) with hT
  have hmem : ∀ θ, dT θ ∈ Formalism.MainNotions.S.UJset ε := fun θ => Kset_sub_UJset ε _ (dT_mem_Kset ε θ)
  have hTadd : ∀ θ θ' v, T (θ + θ') v = T θ (T θ' v) := by
    intro θ θ' v
    simp only [hT, dT_add, hrep.2 _ (hmem θ) _ (hmem θ'), ContinuousLinearMap.comp_apply]
  have hTcomm : ∀ θ θ' v, T θ (T θ' v) = T θ' (T θ v) := by
    intro θ θ' v; rw [← hTadd, ← hTadd, add_comm]
  have hTS : ∀ θ, ∀ v ∈ S, T θ v ∈ S := fun θ v hv => hstab _ (dT_mem_Kset ε θ) v hv

  let P : Submodule ℂ H → Prop := fun W => W ≤ S ∧ W ≠ ⊥ ∧ ∀ θ, ∀ v ∈ W, T θ v ∈ W
  have hex : ∃ k, ∃ W, P W ∧ Module.finrank ℂ W = k := ⟨_, S, ⟨le_rfl, hne, hTS⟩, rfl⟩
  obtain ⟨W, hPW, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' hW'; rw [hWk]; exact Nat.find_min' hex ⟨W', hW', rfl⟩
  have hWfd : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hPW.1

  have hscal : ∀ θ, ∃ c : ℂ, ∀ v ∈ W, T θ v = c • v := by
    intro θ
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hPW.2.1
    let f : Module.End ℂ W := (T θ : H →ₗ[ℂ] H).restrict (fun v hv => hPW.2.2 θ v hv)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hx1 : f x = c • x := Module.End.mem_eigenspace_iff.mp hx.1
    have hx3 : T θ x = c • (x : H) := by
      have := congrArg Subtype.val hx1
      simpa [f] using this
    let E : Submodule ℂ H := W ⊓ Module.End.eigenspace (T θ : H →ₗ[ℂ] H) c
    have hPE : P E := by
      refine ⟨inf_le_left.trans hPW.1, ?_, ?_⟩
      · intro h
        have : (x : H) ∈ E := ⟨x.2, Module.End.mem_eigenspace_iff.mpr hx3⟩
        rw [h, Submodule.mem_bot] at this
        exact hx.2 (Subtype.ext this)
      · intro θ' u hu
        have h2 : T θ u = c • u := Module.End.mem_eigenspace_iff.mp hu.2
        refine ⟨hPW.2.2 θ' u hu.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        show T θ (T θ' u) = c • T θ' u
        rw [hTcomm, h2, map_smul]
    have hEW : E = W := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin E hPE)
    refine ⟨c, fun v hv => ?_⟩
    have : v ∈ E := hEW ▸ hv
    exact Module.End.mem_eigenspace_iff.mp this.2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPW.2.1
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := inner_self_ne_zero.mpr hv0
  set χ : (Fin n → ℝ) → ℂ := fun θ => inner ℂ v (T θ v) / inner ℂ v v with hχ
  have hTv : ∀ θ, T θ v = χ θ • v := by
    intro θ
    obtain ⟨c, hc⟩ := hscal θ
    rw [hc v hvW, hχ]
    simp only [hc v hvW, inner_smul_right]
    rw [mul_div_cancel_right₀ _ hvv]
  have hχeq : ∀ θ c, T θ v = c • v → χ θ = c := by
    intro θ c h
    have := hTv θ
    rw [h] at this
    exact (smul_left_injective ℂ hv0 this).symm
  have hχadd : ∀ θ θ', χ (θ + θ') = χ θ * χ θ' := by
    intro θ θ'
    apply hχeq
    rw [hTadd, hTv θ', map_smul, hTv θ, smul_smul, mul_comm]
  have hχcont : Continuous χ := by
    have h1 : Continuous fun θ => T θ v :=
      (hcont v).comp_continuous continuous_dT hmem
    exact (continuous_const.inner h1).div_const _
  have hχ2 : ∀ a, χ (Pi.single a (2 * Real.pi)) = 1 := by
    intro a; apply hχeq
    simp only [hT, dT_two_pi, hrep.1, ContinuousLinearMap.one_apply, one_smul]
  have hχ0 : χ 0 = 1 := by
    apply hχeq; simp only [hT, dT_zero, hrep.1, ContinuousLinearMap.one_apply, one_smul]

  have hcoord : ∀ a, ∃ m : ℤ, ∀ t : ℝ, χ (Pi.single a t) = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
    intro a
    refine charR_eq_exp (fun t => χ (Pi.single a t)) ?_ ?_ ?_ (hχ2 a)
    · exact hχcont.comp (continuous_single (A := fun _ : Fin n => ℝ) a)
    · intro s t; show χ _ = χ _ * χ _; rw [Pi.single_add, hχadd]
    · simp only [Pi.single_zero, hχ0]
  choose m hm using hcoord
  have hprod : ∀ (s : Finset (Fin n)) (θ : Fin n → ℝ), χ (∑ a ∈ s, Pi.single a (θ a)) = ∏ a ∈ s, χ (Pi.single a (θ a)) := by
    intro s θ
    induction s using Finset.induction_on with
    | empty => simp [hχ0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hχadd, ih]
  refine ⟨fun a => (m a : ℝ), v, hPW.1 hvW, hv0, ?_⟩
  intro θ _
  have h1 : ρ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) v = T θ v := rfl
  rw [h1, hTv]
  congr 1
  have hθ : θ = ∑ a, Pi.single a (θ a) := (Finset.univ_sum_single θ).symm
  rw [hθ, hprod]
  simp only [hm]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.sum_apply, Pi.single_apply]

end GlobalTheory.TorusWtExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportOfPolarisationIdealTimesLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevMoveAA

theorem isMov_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    IsAA Λ ΛT → IsMov m Λ Λ → IsMov m ΛT ΛT := by
  intro D k Λ ΛT m hA hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := _root_.GlobalTheory.HostAAPartition.host_AA_partition D
  have h1 : ∀ i, ∀ x ∈ ΛT, a i • x ∈ Λ := fun i x hx =>
    (hA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, x, hx, rfl⟩)
  have h2 : ∀ i, ∀ x ∈ Λ, c i • x ∈ ΛT := by
    intro i x hx
    have hx' := (hA x).1 hx
    clear hx
    induction hx' using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨a', ha', t, ht, rfl⟩ := hu
      obtain ⟨b, hb⟩ := hc i a' ha'
      rw [smul_smul, ← hb]
      exact ΛT.smul_of_tower_mem b ht
    | zero => simp
    | add x y _ _ ihx ihy => rw [smul_add]; exact ΛT.add_mem ihx ihy
    | neg x _ ihx => rw [smul_neg]; exact ΛT.neg_mem ihx
  have hs1 : ∀ i, ∀ u ∈ hatV ΛT, ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u ∈ hatV Λ :=
    fun i => _root_.GlobalTheory.LevkSmul.smul_mem_hatV D ΛT Λ (a i) (h1 i)
  have hs2 : ∀ i, ∀ u ∈ hatV Λ, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • u ∈ hatV ΛT :=
    fun i => _root_.GlobalTheory.LevkSmul.smul_mem_hatV D Λ ΛT (c i) (h2 i)
  have key : ∀ u : Fin k → AfE D,
      ∑ i, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u = u := by
    intro u
    simp_rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Finset.sum_smul,
      ← TensorProduct.tmul_sum]
    rw [show ∑ i, c i * a i = 1 by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [← Algebra.TensorProduct.one_def, one_smul]
  intro u
  constructor
  · intro hu
    have hw : ∀ i, ∃ w ∈ hatV Λ, ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u = m *ᵥ w :=
      fun i => (hm _).1 (hs1 i u hu)
    choose w hwΛ hwe using hw
    refine ⟨∑ i, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • w i,
      AddSubgroup.sum_mem _ fun i _ => hs2 i _ (hwΛ i), ?_⟩
    rw [Matrix.mulVec_sum]
    conv_lhs => rw [← key u]
    exact Finset.sum_congr rfl fun i _ => by rw [hwe i, Matrix.mulVec_smul]
  · rintro ⟨u₀, hu₀, rfl⟩
    rw [← key u₀, Matrix.mulVec_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact hs2 i _ ((hm _).2 ⟨_, hs1 i u₀ hu₀, rfl⟩)

end GlobalTheory.LevMoveAA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevSLevChiOfFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.FrameTransfer

open Formalism.L2.DIV Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem entry_mem {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) (i j : Fin n) :
    ((β⁻¹ * β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  have key := (hβ (β'.1 *ᵥ Pi.single j 1)).1 ((hβ' _).2 (by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _)) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at key
  exact key

theorem exists_int {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf F E), intGL F E n y = β⁻¹ * β' := by
  set φ := (Formalism.L2.Herm.intAf F E).subtype
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) φ) := fun a b h => by
    ext i j; exact congrArg Subtype.val (Subtype.ext (congrFun (congrFun h i) j))
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ hβ' i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ' hβ i j⟩
  have hM : RingHom.mapMatrix φ M = ((β⁻¹ * β' : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have hM' : RingHom.mapMatrix φ M' = ((β'⁻¹ * β : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have e1 : M * M' = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  have e2 : M' * M = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

theorem st_le {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β' ≤ St β := by
  obtain ⟨y, hy⟩ := exists_int hβ hβ'
  rintro x ⟨z, rfl⟩
  refine ⟨y * z * y⁻¹, ?_⟩
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hy]
  group

theorem st_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β = St β' :=
  le_antisymm (st_le hβ' hβ) (st_le hβ hβ')

section Lev

variable [StarRing E] {LL : Type} [CommRing LL]

theorem mem_parLev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ parLev hc J β D ↔ x ∈ parLev hc J β' D := by
  simp only [parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah, hSt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, hg PP hP x ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, hq PP hP x ▸ (h4 PP hP).2⟩⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, (hg PP hP x).symm ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, (hq PP hP x).symm ▸ (h4 PP hP).2⟩⟩

theorem rTup_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    rTup β D x = rTup β' D x := by
  funext PP
  simp only [rTup, hg PP.1 PP.2 x]

theorem mem_lev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ lev hc J β D ↔ x ∈ lev hc J β' D := by
  show (x ∈ parLev hc J β D ∧ rTup β D x ∈ D.P.H) ↔ (x ∈ parLev hc J β' D ∧ rTup β' D x ∈ D.P.H)
  rw [mem_parLev_iff hSt hg hq, rTup_eq hg]

theorem levFn_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : levFn β D x = levFn β' D x := by
  unfold levFn
  rw [rTup_eq hg]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => by rw [hg PP hP x]
  · exact Finset.prod_congr rfl fun PP hP => by rw [hq PP hP x]

end Lev

end GlobalTheory.FrameTransfer

theorem GlobalTheory.levS_levChi_of_frames : ∀ {D : D7} (V : HSp D) (β β' : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : LevDat D.host.E ℂ V.rank), IsFrame β Λ → IsFrame β' Λ → (∀ PP ∈ L.Pg, ∀ x, redFn β PP x = redFn β' PP x) → (∀ PP ∈ L.Q, ∀ x, redFn β PP x = redFn β' PP x) → ∀ κ : GA D V, (κ ∈ levS V β L ↔ κ ∈ levS V β' L) ∧ levChi V β L κ = levChi V β' L κ := by
  intro D V β β' Λ L hβ hβ' hg hq κ
  have hSt := GlobalTheory.FrameTransfer.st_eq hβ hβ'
  refine ⟨?_, ?_⟩
  · show κ ∈ levG V β L ↔ κ ∈ levG V β' L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [GlobalTheory.FrameTransfer.mem_lev_iff hSt hg hq]
  · unfold levChi
    rw [GlobalTheory.FrameTransfer.levFn_eq hg hq]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPlaces

theorem pg_not_isConjPl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ PP hP PP' hP'
  exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg PP hP PP' hP'

end GlobalTheory.SeeConjPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCMStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  first | exact @GlobalTheory.TrEll.Hasse.rational_eq_local | exact GlobalTheory.TrEll.Hasse.rational_eq_local | (intros; apply GlobalTheory.TrEll.Hasse.rational_eq_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandra
section
namespace GlobalTheory.CoverModel

theorem modelsAreCoverSeries_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  modelsAreCoverSeries

end GlobalTheory.CoverModel
end

