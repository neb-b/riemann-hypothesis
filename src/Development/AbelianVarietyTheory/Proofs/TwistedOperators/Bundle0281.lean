module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParsevalMixedModelIsotropicThetaProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixParsevalPoint

variable {D : D7}

private theorem heisO_apply (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (g : WO S T → ℂ)
    (z : WO S T) : heisO ψ S T w g z = ψ (symplOH S T z w) * g (z + w) := by
  simp only [heisO]

private theorem symplOH_zero_left_twisted_operators (S T : HSp D) (p : WO S T) : symplOH S T 0 p = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (0 : WO S T) 0 p
  rw [zero_add] at h
  linear_combination -h

private theorem mul_mul_conj_mul_eq_of_mul_conj_eq_one (p a b : ℂ) (hp : p * starRingEnd ℂ p = 1) :
    p * a * starRingEnd ℂ (p * b) = a * starRingEnd ℂ b := by
  rw [map_mul]
  linear_combination (a * starRingEnd ℂ b) * hp

theorem psi_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    ψ a * starRingEnd ℂ (ψ a) = 1 := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  norm_num

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  norm_num

theorem symplOH_eq (S T : HSp D) (a b : WO S T) :
    symplOH S T a b = algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T a b := rfl

private theorem heisO_isoPart_incA_add_apply_eq_psi_mul {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) (ψ : AddChar (AF D.host.F) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) (u : Mx D W.rank r)
    (ξ : Matrix (Fin W.rank) (Fin r) D.host.E) (y : Mx D W.rank r) :
    heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f (isoPart V W C y + midPart V V' W B x) =
      ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
        heisO ψ V W (isoPart V W C' u) f (isoPart V W C y + midPart V V' W B x) := by
  have orth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hrat : isoPart V W C' (ξ.map (incA D)) ∈ ratL W V := GlobalTheory.TowerRestrict.isoPart_rat C' ⟨ξ, rfl⟩
  have eXU : symplOH V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) = 0 := by
    rw [symplOH_eq, orth.2.2.2 _ _, mul_zero]
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) f
  rw [eXU, AddChar.map_zero_eq_one, one_smul, ← GlobalTheory.TowerRestrict.isoPart_add C'] at e1
  rw [← e1, heisO_apply ψ (isoPart V W C' (ξ.map (incA D))) (heisO ψ V W (isoPart V W C' u) f),
    add_comm (isoPart V W C y + midPart V V' W B x) _, GlobalTheory.HeisOrtho.heisO_quasi hf _ _ hrat, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
  have s1 := GlobalTheory.TwFour.symplOH_sub V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))
  have s2 := GlobalTheory.TwFour.symplOH_sub V W (midPart V V' W B x) (isoPart V W C' (ξ.map (incA D)))
  have s3 := GlobalTheory.OrientedHeis.symplO_skew (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x)
  rw [orth.2.2.1 _ _, neg_zero] at s3
  rw [s3] at s2
  linear_combination s1 + s2

theorem coef_eq {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x : WO V' W) (u : Mx D W.rank r) (ξ : Matrix (Fin W.rank) (Fin r) D.host.E) :
    res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x =
      ∫ y in 𝓨, ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
        heisO ψ V W (isoPart V W C' u) f (isoPart V W C y + midPart V V' W B x) ∂μ := by
  simp only [res]
  exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y => heisO_isoPart_incA_add_apply_eq_psi_mul hs h1 h2 h3 ψ hf x u ξ y)

theorem res_smul {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (c : ℂ) (g : WO V W → ℂ) (x : WO V' W) : res V V' W C B μ 𝓨 (c • g) x = c * res V V' W C B μ 𝓨 g x := by
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact MeasureTheory.integral_const_mul c _

theorem expand {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x : WO V' W) (u y₀ : Mx D W.rank r) :
    Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E =>
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x‖) ∧
    HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E =>
      ψ (symplO V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀)) *
        res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x)
      (heisO ψ V W (isoPart V W C' u) f (isoPart V W C y₀ + midPart V V' W B x)) := by
  have orth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hUf : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C' u) f) :=
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have hMf : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)) :=
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hUf _
  have hF := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hMf (isoPart V W C y₀)
  obtain ⟨hs1, hs2⟩ := GlobalTheory.TwFour.value_zero_eq_sum_restrictions D V V' W r C C' B hs h1 h2 h3 ψ hψ μ 𝓨 hcov _ hF
  have key : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D)))
        (heisO ψ V W (isoPart V W C y₀) (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)))) 0 =
        ψ (symplO V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀)) *
          res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x := by
    intro ξ
    have eXM : symplO V W (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x) = 0 := orth.2.2.1 _ _
    have eXU : symplOH V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) = 0 := by
      rw [symplOH_eq, orth.2.2.2 _ _, mul_zero]
    have hG : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f)) :=
      GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) _
    rw [GlobalTheory.TwFour.heisO_comm (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀),
      GlobalTheory.TwFour.heisO_comm (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x), eXM, AddChar.map_zero_eq_one,
      one_smul, GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) f, eXU,
      AddChar.map_zero_eq_one, one_smul, ← GlobalTheory.TowerRestrict.isoPart_add C', res_smul,
      GlobalTheory.TowerRestrict.res_heis_iso hs hcov hG, GlobalTheory.TowerRestrict.res_heis_mid hs, heisO_apply,
      symplOH_zero_left_twisted_operators, AddChar.map_zero_eq_one, one_mul, zero_add]
  have hAM : symplOH V W (isoPart V W C y₀) (midPart V V' W B x) = 0 := by
    rw [symplOH_eq, orth.2.1 _ _, mul_zero]
  have F0 : heisO ψ V W (isoPart V W C y₀) (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)) 0 =
      heisO ψ V W (isoPart V W C' u) f (isoPart V W C y₀ + midPart V V' W B x) := by
    rw [heisO_apply, heisO_apply ψ (midPart V V' W B x), symplOH_zero_left_twisted_operators, zero_add, hAM,
      AddChar.map_zero_eq_one, one_mul, one_mul]
  refine ⟨hs1.congr fun ξ => ?_, ?_⟩
  · rw [key ξ, norm_mul, hψ.1.2.1, one_mul]
  · rw [← F0]
    convert hs2 using 1
    funext ξ
    exact (key ξ).symm

theorem parseval_point : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (x : WO V' W) (u : Mx D W.rank r), Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₂) x)‖) ∧ HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₂) x)) (∫ y in 𝓨, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f₂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hcov f₁ f₂ hf₁ hf₂ x u
  have hU₂ := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₂ (isoPart V W C' u)
  obtain ⟨K, hK⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hU₂
  have hμ1 : μ 𝓨 = 1 := hcov.2.2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) := inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hc₂ : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₂) x‖ ≤
        K * (μ.restrict 𝓨).real Set.univ := by
    intro ξ
    rw [coef_eq hs h1 h2 h3 ψ μ 𝓨 hf₂ x u ξ]
    refine MeasureTheory.norm_integral_le_of_norm_le_const (MeasureTheory.ae_of_all _ fun y => ?_)
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hK _
  have hsum₁ := (expand hs h1 h2 h3 hψ hcov hf₁ x u 0).1
  have hcont₂ : Continuous fun y => heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x) :=
    hU₂.3.comp ((GlobalTheory.TowerRestrict.continuous_isoPart C).add continuous_const)
  have hmain : HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ∫ y in 𝓨,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ)
      (∫ y in 𝓨, heisO ψ V W (isoPart V W C' u) f₁ (isoPart V W C y + midPart V V' W B x) *
        starRingEnd ℂ (heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun ξ _ => ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x‖ * K)
      (fun ξ => ?_) (fun ξ => MeasureTheory.ae_of_all _ fun y => ?_) (MeasureTheory.ae_of_all _ fun y => hsum₁.mul_right K)
      (MeasureTheory.integrable_const _) (MeasureTheory.ae_of_all _ fun y => ?_)
    · have hI := GlobalTheory.TowerRestrict.integrable_res (C := C) (B := B) hψ hcov
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₂ (isoPart V W C' (ξ.map (incA D) + u))) x
      have hm : MeasureTheory.AEStronglyMeasurable (fun y => ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) (μ.restrict 𝓨) :=
        hI.aestronglyMeasurable.congr (MeasureTheory.ae_of_all _ fun y => heisO_isoPart_incA_add_apply_eq_psi_mul hs h1 h2 h3 ψ hf₂ x u ξ y)
      exact (Complex.continuous_conj.comp_aestronglyMeasurable hm).const_mul _
    · rw [norm_mul, RCLike.norm_conj, norm_mul, hψ.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
    · have hE := ((expand hs h1 h2 h3 hψ hcov hf₁ x u y).2).mul_right
        (starRingEnd ℂ (heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)))
      convert hE using 1
      all_goals try rfl
      funext ξ
      rw [map_mul, GlobalTheory.OrientedHeis.symplO_skew (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y), conj_psi hψ, neg_neg]
      ring
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ y in 𝓨,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ) =
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₂) x) := by
    intro ξ
    rw [MeasureTheory.integral_const_mul, integral_conj, ← coef_eq hs h1 h2 h3 ψ μ 𝓨 hf₂ x u ξ]
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_)
    (hsum₁.mul_right (K * (μ.restrict 𝓨).real Set.univ)), ?_⟩
  · rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hc₂ ξ) (norm_nonneg _)
  · convert hmain using 1
    · funext ξ
      exact (hterm ξ).symm
    · refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y => ?_)
      dsimp only
      rw [heisO_apply, heisO_apply]
      exact (mul_mul_conj_mul_eq_of_mul_conj_eq_one _ _ _ (psi_mul_conj hψ _)).symm

end GlobalTheory.MixParsevalPoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PureLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finite_of_eq_off {ι : Type} {a b : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite)
    (h : ∀ p, p ≠ q → b p = a p) : (Function.mulSupport b).Finite := by
  refine (ha.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    rw [Function.mem_mulSupport] at hp ⊢
    rwa [h p hpq] at hp

theorem exists_cofactor {ι : Type} {a : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite) :
    ∃ C : ℂ, ∀ b : ι → ℂ, (∀ p, p ≠ q → b p = a p) → ∏ᶠ p, b p = b q * C := by
  refine ⟨∏ᶠ (p) (_ : p ≠ q), a p, fun b hb => ?_⟩
  rw [← mul_finprod_cond_ne q (finite_of_eq_off q ha hb)]
  congr 1
  exact finprod_congr fun p => finprod_congr fun hp => hb p hp

private theorem lineAt_fin_eq_zero_and_inf_other_eq_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) (i : Fin m) (j : Fin n) :
    finPart D (lineAt θ τ z t i j) = 0 ∧ ∀ ρ, ρ ≠ τ → θ ρ (infPart D (lineAt θ τ z t i j)) = 0 := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨by simpa using congrFun (congrFun (hfin t) i) j, fun ρ hρ => ?_⟩
  have h := congrFun (congrFun (hcomp t ρ) i) j
  simp only [hρ, if_false] at h
  simpa [compAt] using h

private theorem ae_eq_zero_of_fin_zero_of_theta_inf_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (a : AE D) (h1 : finPart D a = 0)
    (h2 : ∀ ρ, θ ρ (infPart D a) = 0) : a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact hσ.ext a h1 h2

variable {D : D7}

theorem wAt_lineAt_self {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : wAt (.inr τ) (lineAt θ τ z t) = lineAt θ τ z t := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := _root_.GlobalTheory.PlaceTensor.idem_spec D
  simp only [wAt]
  rw [← sub_eq_zero]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_sub, map_mul, hf]
  · intro ρ
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [(hid.2.2.2.2.2.2 θ hθ ρ).1, one_mul, sub_self]
    · rw [hr ρ hρ, mul_zero, sub_zero]

theorem wAt_lineAt_ne {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) {p : Place D} (hp : p ≠ .inr τ) : wAt p (lineAt θ τ z t) = 0 := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := _root_.GlobalTheory.PlaceTensor.idem_spec D
  simp only [wAt, Matrix.zero_apply, Pi.zero_apply]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_mul, hf]
  · intro ρ
    rw [map_mul, map_mul]
    rcases p with v | τ'
    · rw [(hid.2.2.2.1 v).1, map_zero, zero_mul]
    · have hτ' : τ' ≠ τ := fun h => hp (by rw [h])
      by_cases hρ : ρ = τ'
      · subst hρ
        rw [hr ρ hτ', mul_zero]
      · rw [(hid.2.2.2.2.2.2 θ hθ ρ).2 τ' (Ne.symm hρ), zero_mul]

theorem finite_ne_of_eq_off {ι X : Type} {x y : ι → X} {f₀ : X} (q : ι) (hx : {p | x p ≠ f₀}.Finite)
    (h : ∀ p, p ≠ q → y p = x p) : {p | y p ≠ f₀}.Finite := by
  refine (hx.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    simp only [Set.mem_setOf_eq] at hp ⊢
    rwa [h p hpq] at hp

theorem isPure_linear_and_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → (∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g)) ∧ ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ p, p ≠ .inr τ → x' p = x p) → x' (.inr τ) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ)) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := by
    refine ⟨?_, ?_, hf.cont.add hg.cont, fun k L h1 h2 w => (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)⟩
    · intro γ w
      simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine ⟨?_, ?_, hf.cont.const_smul c, fun k L h1 h2 w => contDiff_const.mul (hf.smooth k L h1 h2 w)⟩
    · intro γ w
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hthH : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨fun x y z f g q c hx hy hyx hzx hzq => ?_, fun x x' f τ z hx hx' hxτ => ?_⟩
  · unfold IsPure IsRestricted at hx hy ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx
    obtain ⟨⟨hyl, -⟩, hgθ, hyw⟩ := hy
    have hzl : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (z p) := by
      intro p
      by_cases hp : p = q
      · rw [hp, hzq]
        exact ((_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hψ hθ (x q) (hxl q).1).2 q (hxl q)).2.1 c (y q) (hyl q)
      · rw [hzx p hp]
        exact hxl p
    refine ⟨⟨hzl, finite_ne_of_eq_off q hxfin hzx⟩,
      theta_add (theta_smul c hfθ) hgθ, fun w => ?_⟩
    obtain ⟨hxs, hxe⟩ := hxw w
    obtain ⟨-, hye⟩ := hyw w
    obtain ⟨C, hC⟩ := exists_cofactor q hxs
    have ha := hC (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) (fun _ _ => rfl)
    have hb := hC (fun p => ipO μ 𝓕 (y p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hyx p hp])
    have hd := hC (fun p => ipO μ 𝓕 (z p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hzx p hp])
    beta_reduce at ha hb hd
    refine ⟨finite_of_eq_off q hxs (fun p hp => by simp only [hzx p hp]), ?_⟩
    have hG := hthH w f₀ hf₀
    have hGq := hthH (wAt q w) f₀ hf₀
    have e1 := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ (c • f) (heisO ψ S T w f₀) (theta_smul c hfθ) hG
    have e2 := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w f₀) hfθ hG
    have e3 := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ (c • x q) (heisO ψ S T (wAt q w) f₀)
      (theta_smul c (hxl q).1) hGq
    have e4 := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ (x q) (heisO ψ S T (wAt q w) f₀) (hxl q).1 hGq
    rw [hd, hzq, (e3.2.2.2.1 (y q) (hyl q).1).1, (e4.2.2.1 c).1, (e1.2.2.2.1 g hgθ).1, (e2.2.2.1 c).1,
      hxe, hye, ha, hb]
    ring
  · have hx1 := hx
    unfold IsPure IsRestricted at hx1 ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx1
    have hx'l : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (x' p) := by
      intro p
      by_cases hp : p = .inr τ
      · rw [hp, hxτ]
        exact ((_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hψ hθ (x (.inr τ)) (hxl _).1).2 (.inr τ) (hxl _)).2.2 τ rfl z
      · rw [hx' p hp]
        exact hxl p
    refine ⟨⟨hx'l, finite_ne_of_eq_off (.inr τ) hxfin hx'⟩,
      GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hfθ, fun w => ?_⟩
    obtain ⟨hxs, -⟩ := hxw w
    obtain ⟨C, hC⟩ := exists_cofactor (.inr τ) hxs
    have key : ∀ t : ℝ, ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀) =
        ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C := by
      intro t
      have hP := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx (lineAt θ τ z t)
      unfold IsPure at hP
      have e := hC (fun p => ipO μ 𝓕 (heisO ψ S T (wAt p (lineAt θ τ z t)) (x p)) (heisO ψ S T (wAt p w) f₀))
        (fun p hp => by simp only [wAt_lineAt_ne hθ τ z t hp, GlobalTheory.WeilVacMove.heisO_zero])
      beta_reduce at e
      rw [(hP.2.2 w).2, e, wAt_lineAt_self hθ τ z t]
    have hG := hthH w f₀ hf₀
    have h1 := (_root_.GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew D ψ θ S T μ 𝓕 hψ hθ hμ f (heisO ψ S T w f₀) hfθ hG τ z).1
    have h2 := ((_root_.GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew D ψ θ S T μ 𝓕 hψ hθ hμ (x (.inr τ)) (heisO ψ S T (wAt (.inr τ) w) f₀)
      (hxl _).1 (hthH _ _ hf₀) τ z).1).mul_const C
    have h3 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀))
        (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C) 0 := by
      simpa only [key] using h2
    have hd := hC (fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hx' p hp])
    beta_reduce at hd
    refine ⟨finite_of_eq_off (.inr τ) hxs (fun p hp => by simp only [hx' p hp]), ?_⟩
    rw [hd, hxτ, h1.unique h3]

end GlobalTheory.PureLinear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.ArchVanish

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

variable {σ J}

theorem isMulCommutative_cent_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsMulCommutative (Orb.cent (projArch σ J w (ratEmb σ J γ))) :=
  Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)


end General

end GlobalTheory.ArchVanish

end

namespace GlobalTheory.ArchVanish


end GlobalTheory.ArchVanish
end

