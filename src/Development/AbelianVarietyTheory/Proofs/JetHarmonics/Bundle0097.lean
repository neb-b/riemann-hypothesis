module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem exists_shifted_types_lower_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ k r z π u l n₀ b hz hT hπ hreg hl1 hlk hgap hb hn hb1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : m < n := by omega
  let i : Fin n := ⟨m, hm⟩
  obtain ⟨β, L, hL, hu, hd⟩ := GlobalTheory.exists_int_coords_of_regular_param n u (by simpa using hreg)
  obtain ⟨B, hB⟩ := (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).1
  have hgapZ : L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc := by
    have h := hd i.castSucc i.succ
    simp only [Fin.val_succ, Fin.val_castSucc, i] at h
    have : ((L i.succ + 2 * (n₀ : ℤ) + 1 : ℤ) : ℝ) ≤ ((L i.castSucc : ℤ) : ℝ) := by
      push_cast
      simp only [i]
      linarith
    exact_mod_cast this
  have hwide : (L 0 : ℝ) - (L (Fin.last n) : ℝ) ≤ 2 * b := by
    rw [hd]
    have h1 := abs_le.mp (hb (((0 : Fin (n + 1)) : ℕ) + 1) (by simp))
    have h2 := abs_le.mp (hb (((Fin.last n : Fin (n + 1)) : ℕ) + 1) (by simp))
    linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, πp, Ap, hπp, hAp, hwp⟩ :=
    _root_.GlobalTheory.WigSh.chain_raise V n r z π u β L B i.succ n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : j ≤ i.castSucc := Fin.le_castSucc_iff.mpr hj
      have := hL.antitone hj'
      omega)
  obtain ⟨Vm, familyMassRatio, familyMassSecondLine, iM3, πm, Am, hπm, hAm, hwm⟩ :=
    _root_.GlobalTheory.WigSh.exists_wigMap_chain_lowering V n r z π u β L B i.castSucc n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
      have := hL.antitone hj'
      omega)
  refine ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, ?_⟩
  refine GlobalTheory.WigSh.lower_bound_spreads V Vp Vm n r z π πp πm B Ap Am n₀ b hz hT hπ.2.2.2.1 hπp.2.2.2.1
    hπm.2.2.2.1 hB hAp hAm ?_
  intro v
  have hyp := (GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB).1
  have hdec := (Formalism.FourierDecayAlt.P.branching_decomposition V n (EB π B) β L hyp).2
  have hspan : ⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA (EB π B)) (shf β M.1) = ⊤ := by
    rw [← hdec, iSup_subtype]
  have key := GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces V Vp Vm {M : Fin n → ℤ // Box L M}
    (fun M => CapSp (subA (EB π B)) (shf β M.1)) (Ap (B (Fin.last n))) (Am (B (Fin.last n))) _ _
    ((3 * b) ^ (2 * n₀))⁻¹ hspan (fun M w hw => ⟨hwp M.1 w hw, hwm M.1 w hw⟩)
    (fun M => GlobalTheory.WigSh.chain_lower_bound n L M.1 i n₀ b hL M.2 hgapZ hb1 hn hwide) v
  have hpos : 0 < (3 * b) ^ (2 * n₀) := by positivity
  rwa [inv_mul_le_iff₀ hpos] at key

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowthStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_l2_bound_and_isometry : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  first | exact @GlobalTheory.MomMass.mom_mass | exact GlobalTheory.MomMass.mom_mass | (intros; apply GlobalTheory.MomMass.mom_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentGrowth
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DualStepBound

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1 : Fin n → ℤ) ≤ n1 ν + 1 := by
  unfold n1
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa using Int.natAbs_sub_le (ν i) ((Pi.single s 1 : Fin n → ℤ) i)

theorem sum_mem_sm {k r : ℕ} (R : Rep k r) {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (fun c _ => hx c)

theorem dual_step_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s κ₀ hκ
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hν1 : ∀ t, n1 (ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) ≤ q0 :=
    fun t => (lOneNorm_sub_single_one_le ν t).trans hν
  have hDS : (R ν).IsDS _ _ := hFam ν hν0
  have hDS1 : ∀ t, (R (ν - Pi.single t 1)).IsDS (PI.BesselPeriodGGP.eps48 k r)
      (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := fun t => hFam _ (hν1 t)
  have hpar : ∀ t, (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ))
      = (fun a => lam a + (ν a : ℝ)) - Pi.single t 1 := by
    intro t
    funext a
    by_cases hat : a = t
    · subst hat
      simp
      ring
    · simp [Pi.single_eq_of_ne hat]
  have hDS2 : ∀ t, (R (ν - Pi.single t 1)).IsDS (PI.BesselPeriodGGP.eps48 k r)
      ((fun a => lam a + (ν a : ℝ)) - Pi.single t 1) := fun t => hpar t ▸ hDS1 t
  obtain ⟨hBe, hdg, hdeg⟩ := hSF ν hν0
  obtain ⟨hBe1, hdg1, hdeg1⟩ := hSF _ (hν1 s)
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.dual_tensor_bessel_moment hH k r _ _ (R ν) (fun s => R (ν - Pi.single s 1)) io pr Wp z π u
    μW μN μG νq (l ν) hNum.1 hDS hDS2 hT.raw hSide hBe.1 s
  have hdual := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1))
    io pr ep _ _ _ Wp z π u μW μN μG νq (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDS2
    (GlobalTheory.isFRep_dualM k r) hT hSide
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hSide.1 g hg).2) hBe hnz s
    (l (ν - Pi.single s 1)) hBe1).2 κ₀ hκ
  obtain ⟨v, hv, hv0⟩ := hnz
  have hy : ∑ d, pr s d (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) ∈ (R (ν - Pi.single s 1)).sm :=
    sum_mem_sm _ _ fun d => (hT.raw.pr_sm s d).mem _ ((R ν).smSub.smul_mem _ hv)
  have e1 := hdual _ hy
  rw [hcv v hv, hκ v hv, smul_smul] at e1
  have e2 : c = (ep s : ℂ) * star κ₀ * κ₀ := smul_left_injective ℂ hv0 e1
  have hep : ‖(ep s : ℂ)‖ = 1 := by
    rcases hT.ep_sq s with h' | h' <;> simp [h']
  have e3 : ‖κ₀‖ ^ 2 = ‖c‖ := by
    rw [e2, norm_mul, norm_mul, hep, norm_star]; ring
  obtain ⟨c₀, hc₀, hdegs⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r (PI.BesselPeriodGGP.eps48 k r) μG
    hSide.2.2.2.2.2.2.1
  have hKS : PI.KFinSmooth := hH.1.2.2.1
  have d0 : dg ν = c₀ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg w hw0, (hdegs _ _ hDS).1 w hw0]
  have d1 : dg (ν - Pi.single s 1) = c₀ * Formalism.QuantumDeterminants.fdegHC
      (fun a => lam a + ((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ (hDS1 s)).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg1 w hw0, (hdegs _ _ (hDS1 s)).1 w hw0]
  have hratio := (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hNum ν hν0).2.2 s
  have hp7 := GlobalTheory.PieriBound.lowering_bound k r lam u b bv ga h q0 hNum ν hν0 s
  have hgap := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.2.2
  have hB : (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => abs_ne_zero.2 ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ht) with h' | h'
    · have := hgap t s h'
      linarith
    · have := hgap s t h'
      linarith
  rw [Finset.prod_div_distrib] at hratio
  have hq : dg ν / dg (ν - Pi.single s 1)
      = (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) /
        ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| := by
    rw [d0, d1, mul_div_mul_left _ _ hc₀.ne', ← inv_div, hratio, inv_div]
  rw [mul_div_assoc, hq, e3, hc, mul_assoc, div_mul_div_cancel₀ hB]
  exact mul_le_mul_of_nonneg_left hp7 hSide.2.1.le

end GlobalTheory.DualStepBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqOneOfMultilinear
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem pow_eq_one_of_multilinear {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {j : ℕ} (bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => M) N)
    (hspan : ∀ S : N, S ∈ Submodule.span F {S' | ∃ s, S' = bx s})
    (U : Fin j → Module.End F M) (W : Module.End F N)
    (hW : ∀ s, W (bx s) = bx (fun i => U i (s i)))
    (hU : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ U i ^ m = 1) : ∃ m : ℕ, 1 ≤ m ∧ W ^ m = 1 := by
  classical
  choose m hm hU using hU
  have hp : ∀ (n : ℕ) s, (W ^ n) (bx s) = bx (fun i => (U i ^ n) (s i)) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ', Module.End.mul_apply, ih, hW]
      simp only [pow_succ', Module.End.mul_apply]
  refine ⟨∏ i, m i, Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hm i; omega), LinearMap.ext fun S => ?_⟩
  refine LinearMap.eqOn_span' (s := {S' | ∃ s, S' = bx s}) ?_ (hspan S)
  rintro _ ⟨s, rfl⟩
  rw [hp]
  have : ∀ i, U i ^ (∏ i, m i) = 1 := fun i => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    rw [hc, pow_mul, hU, one_pow]
  simp only [this, Module.End.one_apply]

theorem finOrd_box : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (w : ∀ i, LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F (p i).g.b) (DegPre.lineε k))) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε k))), (∀ i, (w i).IsGen) → w'.IsGen → (∀ (s s₁ : Fin j → Fam D.toPre F k) (S S₁ : Fam D'.toPre F k), (∀ i, PhiRel D.toPre F k (p i) (w i) (s i) (s₁ i)) → IsBoxFam pD F k S s → IsBoxFam pD F k S₁ s₁ → PhiRel D'.toPre F k p' w' S S₁) → ∀ ζ : Fin j → F, (∀ i, FinOrd D F k (p i) (w i) (ζ i)) → FinOrd D' F k p' w' (∏ i, ζ i) := by
  intro hL hL2 hL4 hT V _ _ _ _ j D D' pD F _ _ k hk p' p _ w w' hw hw' hc ζ h
  have hG := hL.globalFns
  obtain ⟨bx, hbx⟩ := GlobalTheory.T.exists_boxFamily_multilinear_map hG V j D.toPre D'.toPre pD F k
  have hspan := _root_.GlobalTheory.mem_span_boxFam hL hL2 hL4 hT V j D D' pD F k hk
  simp only [hbx] at hspan
  choose Φ hΦ using fun i => phiFun_of_globalFns hG V _ D F k hk (p i) (w i) (hw i)
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D' F k hk p' w' hw'
  refine (ThetaFinOrd.finOrd_iff p' w' _ Φ' hΦ').2 (pow_eq_one_of_multilinear bx hspan
    (fun i => ζ i • Φ i) _ (fun s => ?_)
    (fun i => (ThetaFinOrd.finOrd_iff (p i) (w i) _ (Φ i) (hΦ i)).1 (h i)))
  have e := (hΦ' _ _).1 (hc s (fun i => Φ i (s i)) _ _ (fun i => (hΦ i _ _).2 rfl)
    ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  simp only [LinearMap.smul_apply]
  rw [← e, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullLin

theorem stalkMap_injective_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem sec_eq_zero_of_flat {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (f : Y' ⟶ Y) [Flat f] [Surjective f]
    (h : ∀ x J, Good L x J → sval s f x J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  apply stalkMap_injective_of_flat f x
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ x)
  refine (gs_stalkMap f x _ hy _).symm.trans (Eq.trans ?_ (gs_stalkMap f x _ hy _))
  refine (sec_trans s f x hy (Good.mem hJ φ f)).trans ?_
  refine (congrArg _ (h x J hJ)).trans ((mul_zero _).trans ?_)
  rw [gs_eq f x _ hy, map_zero, map_zero]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left :=
  congrArg (fun q => q.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem aF_snd (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
  congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem isPullback_aF (oa : D.toPre.OAct O) (a : O) :
    IsPullback (aF D F oa a).left (DegPre.prB D.toPre F).left (DegPre.prB D.toPre F).left (oa.onB.act a).left := by
  have h₀ : IsPullback (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.prB D.toPre F).left
      (TF (R := V) F).hom D.toPre.P.A.hom := IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (aF_snd oa a) h₀
  rw [aF_fst, Over.w]
  exact h₀

theorem aF_mul (oa : D.toPre.OAct O) (a b : O) : aF D F oa (a * b) = aF D F oa b ≫ aF D F oa a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, DegPre.prB, oa.onB.map_mul]

theorem pullAl_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine gen_unique' D.toPre.P.isLB (fun _ _ _ => rfl) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left (congrArg (fun q => q.left) z₁) (surj_appTop D.toPre F hG) hu hu'
    (fun y I hI => ?_) Z r z J hJ
  have a₁ := val_corr hI c (𝟙 _)
  have a₂ := val_corr hI c' (𝟙 _)
  rw [val_pull hI, Category.id_comp] at a₁ a₂
  exact a₁.trans a₂.symm

theorem pullAl_unique (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s t') : t = t' := by
  refine fam_ext fun β j => ?_
  by_cases hβ : ∃ χ, β = star a • χ
  · obtain ⟨χ, rfl⟩ := hβ
    obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
    rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu hu' c c' _ _ y J hJ]
  · exact (h.2 β (fun χ e => hβ ⟨χ, e⟩) j).trans (h'.2 β (fun χ e => hβ ⟨χ, e⟩) j).symm

theorem pullAl_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_add _ _ _ _ y hJ, sval_add _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu' hu c' c _ _ y J hJ, add_mul]
  · rw [add_f, h.2 β hβ j, h'.2 β hβ j, add_zero]

theorem pullAl_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_smul _ _ _ _ y hJ, sval_smul _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ, Category.assoc, aF_fst, _root_.mul_assoc]
  · rw [smul_f, h.2 β hβ j, mul_zero]

theorem eq_zero_of_pullAl_zero (hM : MulNSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (haa : a * star a = (N : O)) {s : Fam D.toPre F k} (h : PullAl D F oa a k N s 0) : s = 0 := by
  obtain ⟨-, hflat, hsurj, -⟩ := hM _ D.toPre.P N hN
  have hm : oa.onB.act (a * star a) = mulA D.toPre.P.A N := by
    rw [haa, ← _root_.mul_one (N : O), act_nsmul, oa.onB.map_one]
  rw [← hm] at hflat hsurj
  have hp := isPullback_aF (F := F) oa (a * star a)
  have : Flat (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hflat
  have : Surjective (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hsurj
  refine fam_ext fun χ j => sec_eq_zero_of_flat D.toPre.P.isLB (s.s χ) (aF D F oa (a * star a)).left
    (fun x J hJ => ?_) j
  obtain ⟨u, -, -, e⟩ := h.1 χ
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (aF D F oa (star a)).left x J hJ
  have e₀ : sval ((0 : Fam D.toPre F (k * N)).s (star a • χ)) (aF D F oa (star a)).left x J = 0 :=
    gs_zero _ x _ (hJ.mem _ _)
  rw [e₀, ← Over.comp_left, ← aF_mul] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

theorem exists_pull_linearMap : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O]
    [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 →
    ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) →
    ∃ π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N), Function.Injective π ∧
      ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw a N k hN _ haa
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := id hw
  choose P hP using fun s : Fam D.toPre F k => exists_pullAl D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k s
    (pullSecs_fe' D F hG D.toPre.P.isLB oa w0 hw uΨ huΨ a N haa hN k s)
  let π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N) :=
    { toFun := P
      map_add' := fun s s' => pullAl_unique hG oa a k N (hP _) (pullAl_add hG oa a k N (hP s) (hP s'))
      map_smul' := fun ζ s => pullAl_unique hG oa a k N (hP _) (pullAl_smul oa a k N ζ (hP s)) }
  refine ⟨π, (injective_iff_map_eq_zero π).2 fun s hs => ?_, fun s s' =>
    ⟨fun h => pullAl_unique hG oa a k N h (hP s), fun h => h ▸ hP s⟩⟩
  exact eq_zero_of_pullAl_zero hL.mulN oa a k N hN haa (hs ▸ hP s)

end GlobalTheory.PullLin
end
end

