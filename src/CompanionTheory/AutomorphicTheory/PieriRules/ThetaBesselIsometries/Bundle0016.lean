module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0040
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0015
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0011
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0013
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0004
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0009
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0010
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyMoment
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentStep

theorem lintegral_le_of_le_sum {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : Ω → ℝ)
    (g : ι → ι → Ω → ℝ) (C : ℝ) (N : ι → ι → ℝ) (hC : 0 ≤ C) (hg0 : ∀ d s x, 0 ≤ g d s x)
    (hm : ∀ d s, AEMeasurable (g d s) ν) (hpt : ∀ᵐ x ∂ν, f x ≤ C * ∑ d, ∑ s, g d s x)
    (hN : ∀ d s, 0 ≤ N d s) (hint : ∀ d s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν ≤ ENNReal.ofReal (N d s)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal (C * ∑ d, ∑ s, N d s) := by
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (g d s x) ∂ν := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hg0 d s x]
        congr 1
        exact Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hg0 d s x
    _ = ENNReal.ofReal C * ∑ d, ∑ s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun d _ => Finset.aemeasurable_fun_sum _ fun s _ => (hm d s).ennreal_ofReal]
        congr 1
        exact Finset.sum_congr rfl fun d _ => lintegral_finsetSum' _ fun s _ => (hm d s).ennreal_ofReal
    _ ≤ ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (N d s) := by
        gcongr with d _ s _
        exact hint d s
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hN d s]
        congr 1
        exact (Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hN d s).symm

theorem norm_sum_smul_sq_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ)
    (v : ι → V) : ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2 := by
  have h1 : ‖∑ s, c s • v s‖ ≤ ∑ s, ‖c s‖ * ‖v s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_smul _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun s => ‖c s‖ * ‖v s‖)
  simp only [mul_pow, Finset.card_univ] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem pointwise_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (L D A : ℝ) (q : ℕ)
    (a β : ι → ℂ) (Ds : ι → ℝ) (v : V) (y : ι → ι → V) (hD : 0 ≤ D) (hL : ∑ d, ‖a d‖ ^ 2 = L ^ 2)
    (he : ∀ d, a d • v = ∑ s, β s • y d s) (hβ : ∀ s, ‖β s‖ ^ 2 * D ≤ A * Ds s) :
    L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * A) * ∑ d, ∑ s, L ^ (2 * q) * (Ds s * ‖y d s‖ ^ 2) := by
  have hP : 0 ≤ L ^ (2 * q) := by rw [pow_mul]; positivity
  have e1 : L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) = ∑ d, L ^ (2 * q) * (D * ‖a d • v‖ ^ 2) := by
    rw [mul_add, pow_add, mul_one, ← hL, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [norm_smul]; ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [he d]
  calc L ^ (2 * q) * (D * ‖∑ s, β s • y d s‖ ^ 2)
      ≤ L ^ (2 * q) * (D * ((Fintype.card ι : ℝ) * ∑ s, ‖β s‖ ^ 2 * ‖y d s‖ ^ 2)) := by
        gcongr
        exact norm_sum_smul_sq_le β (y d)
    _ = ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (‖β s‖ ^ 2 * D) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (A * Ds s) := by
        exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hβ s) (by positivity)
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) : n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem param_sub_single {n : ℕ} (lam : Fin n → ℝ) (ν : Fin n → ℤ) (s : Fin n) :
    (fun a => lam a + (((ν - Pi.single s 1) : Fin n → ℤ) a : ℝ)) =
      (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp; ring
  · simp [h]


set_option maxHeartbeats 1000000 in
theorem moment_step : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q MM hj hMM hind w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hNum, hFam, hG, hSide⟩ := id hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hνs : ∀ s, n1 (ν - Pi.single s 1) ≤ q0 := fun s => (lOneNorm_sub_single_one_le ν s).trans hν
  have hDS := hFam ν hν0
  have hDSs := fun s => hFam _ (hνs s)
  obtain ⟨hBe, hdg, -⟩ := hSide ν hν0
  have hBes := fun s => (hSide _ (hνs s)).1
  have hdgs := fun s => (hSide _ (hνs s)).2.1
  obtain ⟨hae, -, hmL, hml⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  by_cases hnz : NzOn (R ν) (l ν)
  swap
  · have : ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) *
        (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae (hae.mono fun x hx => ?_)
      have : l ν ((R ν).σ (Matrix.of x) w) = 0 := by
        by_contra hne
        exact hnz ⟨_, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hDS.2 w.2 hx, hne⟩
      simp [this]
    rw [this]
    exact bot_le
  obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH k r lam u b bv ga h q0 R hNum hFam ν).2 hν
  have hF := GlobalTheory.isFRep_dualM k r
  have hkap := fun s => GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν)
    (fun s => R (ν - Pi.single s 1)) io pr ep _ _ _ Wp z π u μW μN μG νq
    (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDSs hF hT hG
    (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).2) hBe hnz s
    (l (ν - Pi.single s 1)) (hBes s)
  choose κ hκ using fun s => (hkap s).1
  have hdual := fun s => (hkap s).2 (κ s) (hκ s)
  have hA : ∀ s, ‖(ep s : ℂ) * star (κ s)‖ ^ 2 * dg ν ≤
      (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * dg (ν - Pi.single s 1) := by
    intro s
    have h1 := GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s
      (κ s) (hκ s)
    rw [div_le_iff₀ (hdgs s)] at h1
    have h2 : ‖(ep s : ℂ) * star (κ s)‖ = ‖κ s‖ := by
      rcases hT.ep_sq s with h | h <;> simp [h]
    rwa [h2]
  obtain ⟨io', pr', hAlg, hpr⟩ := GlobalTheory.T.dual_tensor_cayley_weighted hK k r _ _ (R ν) hDS (fun s => R (ν - Pi.single s 1)) _ io pr ep Q
    (E ν) (fun s => E (ν - Pi.single s 1)) hDSs hT hQ (hE ν hν0).1 (fun s => (hE _ (hνs s)).1)
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν0).1
  have hMods : ∀ s, IsMod (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1))
      ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := fun s => by
    rw [← param_sub_single]
    exact GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ _ hNum.1 (hDSs s) Q _ hQ (hE _ (hνs s)).1
  have hShape := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.1
  have hlev := _root_.GlobalTheory.lev_proj_and_sum_sq_le _ _ _ (E ν) (fun s => (R (ν - Pi.single s 1)).smSub) (fun s => E (ν - Pi.single s 1))
    io' pr' _ k j bv w hMod hMods hAlg hShape hj hw
  have hexp : 2 * r + k + 1 + 1 - k = 2 * r + 2 := by omega
  rw [hexp] at hlev
  have hy : ∀ d s, ((pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub) : (R (ν - Pi.single s 1)).H) =
      ∑ c, pr s c (tm (R ν) (fun c => Q d c) w c) := by
    intro d s
    rw [hpr]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [Finset.sum_eq_single d]
    · simp [tm]
    · intro e _ he; simp [he]
    · simp
  have hA0 : 0 ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := mul_nonneg hG.2.1.le (by positivity)
  have key := lintegral_le_of_le_sum νq
    (fun x => lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2))
    (fun d s x => lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) *
      ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x)
        (pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub))‖ ^ 2))
    ((Fintype.card (Fin (2 * r + k + 1)) : ℝ) * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4))
    (fun d s => MM * ‖pr' s (Pi.single d w)‖ ^ 2) (by positivity)
    (fun d s x => mul_nonneg (by rw [pow_mul]; positivity) (mul_nonneg (hdgs s).le (by positivity)))
    (fun d s => ((hmL 0).pow_const _).mul
      ((((GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ _ Wp z π u μW μN μG νq (hDSs s) hG).2.2.2 _ (hBes s).1 _
        (pr' s (Pi.single d w)).2).norm.aemeasurable.pow_const _).const_mul _))
    (hae.mono fun x hx => by
      refine pointwise_le _ _ _ q
        (fun d => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (dualM (Matrix.of x) *ᵥ (fun c => Q d c))
          (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)))
        (fun s => (ep s : ℂ) * star (κ s)) _ _ _ hdg.le ?_ (fun d => ?_) hA
      · rw [_root_.GlobalTheory.MomentParseval.sum_herm_sq k r _ dualM _ Q 1 _ hF hQ.2 _ hx]
        exact (GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).2.1
      · simp only [hy]
        exact GlobalTheory.T.tensor_bessel_transfer hK k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1)) io pr _ _ _
          Wp _ (l ν) (fun s => l (ν - Pi.single s 1)) _ hDS hDSs hT.raw hBe.1.1 hBe.1.2.1 hdual _ w w.2 _ hx)
    (fun d s => by positivity)
    (fun d s => hind s _ (by rw [param_sub_single]; exact (hlev d).1 s))
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : ∑ d, ∑ s, MM * ‖pr' s (Pi.single d w)‖ ^ 2 ≤
      ∑ _d : Fin (2 * r + k + 1), MM * ((6 * bv) ^ (2 * (2 * r + 2)) * ‖w‖ ^ 2) := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hlev d).2 hMM
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.MomentStep
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentWeighted
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomLem8

theorem ev_col {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ) (hH : Γᴴ = Γ)
    (h2 : Γ * Γ = 1) (R : BranchingSupport.Rep k r) (x : ι → R.H) (e : ι) :
    ev Γ R (fun c => Γ c e) x = x e := by
  unfold ev
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, (star (Γ i e) * Γ i j) = if e = j then 1 else 0 := by
    intro j
    have h := congrFun (congrFun h2 e) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (Γ i e) = Γ e i := by
      have := congrFun (congrFun hH e) i
      rwa [Matrix.conjTranspose_apply] at this
    rw [this]
  simp_rw [← Finset.sum_smul, key]
  simp

theorem transpose_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ) (hH : Γᴴ = Γ)
    (h2 : Γ * Γ = 1) : Γᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have : (Γᵀ)ᴴ = Γᵀ := by
    rw [show (Γᵀ)ᴴ = (Γᴴ)ᵀ from rfl, hH]
  rw [this, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

theorem div_step (b t : ℝ) (ht : 0 ≤ t) (L : ℝ≥0∞)
    (h : ENNReal.ofReal (b * t * t) ≤ L * ENNReal.ofReal t) : ENNReal.ofReal (b * t) ≤ L := by
  rcases ht.eq_or_lt with h0 | h0
  · simp [← h0]
  · rw [ENNReal.ofReal_mul' ht] at h
    exact (ENNReal.mul_le_mul_iff_left (by simpa using h0) ENNReal.ofReal_ne_top).1 h

theorem moment_lemma_pieri : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal ((∑ i, ‖(ρ (Matrix.of x)⁻¹ *ᵥ om) i‖ ^ 2) * ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
  intro hy k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hρ hT
    hS hB hBI hβ I hI y hy'
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hadj, -, hev, hnorm, -⟩ :=
    GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hρ hT
  obtain ⟨hae, hcont, -, hmB⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS
  obtain ⟨-, -, -, hmI⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (hRI I) hS
  have hf := hmI (BI I) hI.1 y hy'
  have hH := hρ.1
  have h2 := hρ.2.1
  have hc := hρ.2.2.2.2.2.1
  have hph : ∀ e, AEStronglyMeasurable
      (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ fun c => Γ c e) om) νq := by
    intro e
    refine hcont ℂ (fun g => Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ fun c => Γ c e) om) ?_
    simp only [Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ?_
    exact continuousOn_finsetSum _ fun l _ => (hc j l).mul continuousOn_const
  have hstep : ∀ e, ENNReal.ofReal (‖β I‖ ^ 2 * ‖io I e y‖ ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (‖Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ fun c => Γ c e) om‖ ^ 2 *
        ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
    intro e
    have hw : io I e y ∈ R.sm := (hT.raw.io_sm I e).mem y hy'
    have hpair := GlobalTheory.T.tensor_moment_transfer hy k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π u μW μN μG νq om Bm BI β hR hRI hinj
      hT.raw hS hB.1 hBI hβ I hI y hy' (fun c => Γ c e) (io I e y) hw
    have hcs := GlobalTheory.T.norm_sq_integral_inner_weight_le (Formalism.QuantumDeterminants.Mt k r) Wp νq _ _ _ hf (hmB Bm hB.1 _ hw) (hph e)
    rw [hpair] at hcs
    have hiso := hB.2 _ hw
    have hg : ∫⁻ x, ENNReal.ofReal (‖Bm (R.σ (Matrix.of x) (io I e y))‖ ^ 2) ∂νq =
        ENNReal.ofReal (‖io I e y‖ ^ 2) := by
      rw [← hiso]
      unfold PI.BesselPeriodGGP.l2SG
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    rw [hg] at hcs
    have h1 := hadj I y hy' (tm R (fun c => Γ c e) (io I e y)) (fun c => R.smSub.smul_mem _ hw)
    rw [hev, ev_col Γ hH h2] at h1
    have h3 : ‖⟪y, ∑ c, pr I c (tm R (fun c => Γ c e) (io I e y) c)⟫_ℂ‖ = ‖io I e y‖ ^ 2 := by
      rw [norm_inner_symm]
      have h4 := congrArg norm h1
      have hep : ‖(ep I : ℂ)‖ = 1 := by
        rcases hT.ep_sq I with h | h <;> simp [h]
      rw [norm_mul, hep, one_mul, inner_self_eq_norm_sq_to_K] at h4
      rw [← h4]
      simp
    rw [norm_mul, h3] at hcs
    refine div_step _ _ (by positivity) _ ?_
    convert hcs using 2
    ring
  have hsum : ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∑ e, ENNReal.ofReal (‖β I‖ ^ 2 * ‖io I e y‖ ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity), ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hnorm I y hy') (by positivity))
  refine hsum.trans ((Finset.sum_le_sum fun e _ => hstep e).trans (le_of_eq ?_))
  rw [← lintegral_finsetSum']
  · refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity), ← Finset.sum_mul]
    have := _root_.GlobalTheory.MomentParseval.sum_herm_sq k r ι ρ Γ Γᵀ d om hρ (transpose_unitary Γ hH h2) _ hx
    rw [← this]
    rfl
  · intro e _
    exact (((hph e).norm.aemeasurable.pow_const 2).mul (hf.norm.aemeasurable.pow_const 2)).ennreal_ofReal

end GlobalTheory.MomLem8
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorWeightedBesselGapStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_weighted_bessel_gap : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDG ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  first | exact @GlobalTheory.BesselPieri.pieri_bessel | exact GlobalTheory.BesselPieri.pieri_bessel | (intros; apply GlobalTheory.BesselPieri.pieri_bessel <;> assumption)
end Gp91
end

