module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MaximalCompactConjugacy.Assembly
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0018
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianCovectors.HermBvecLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.ClassSetFinIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.CTFromBlocks
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.ModelMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantDeterminantScaling.IntCastMulEqSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.SkipOneEqSuccAbove
public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantLinearProduct.OfFnProdSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DerivativePreservation.EabPresMain
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RightSingleRule.EllSingleZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.SecondHermitianPartDiagonal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeMaxCpt
section
theorem adelic_maximal_compact : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I :=
  PI.BridgeMaxCptWork.bridgeMaxCpt_of adelic_compact_real_places adelic_compact_finite_places
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovecEntries
section
theorem covector_entries : Formalism.FourierDecayAlt.C3.XiYZhat := CovecW.covec_entries
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InHHClassFin
section
theorem stabClassFinite : PI.InHHClassFin.StabClassFinite :=
  PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps
    (fun _ _ Γ K K' h => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono Γ K K' h)
    (fun _ _ Γ K K' h hi => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_finIdx Γ K K' h hi)
    (fun _ _ _ _ Φ Γ K => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map Φ Γ K)
    PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd PI.UnitaryGroupMassFormula.InHHClassFin.sigConj PI.UnitaryGroupMassFormula.InHHClassFin.frameExists
    PI.UnitaryGroupMassFormula.InHHClassFin.frameIso PI.UnitaryGroupMassFormula.InHHClassFin.frameGram PI.UnitaryGroupMassFormula.InHHClassFin.frameRat
    PI.UnitaryGroupMassFormula.InHHClassFin.levelStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ModelIso
section
theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso :=
  fun hp hu hh => PI.WMI.modelIso_of_steps (PI.WMI.polyExt_of hp hu) PI.WMI.lambda_integrality
    PI.WMI.torus_eigenvalue_formula PI.WMI.lower_triangular_invariance PI.WMI.model_map_equivariance PI.WMI.determinant_splitting_formula hh
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
section
theorem covariant_det_of_lin : PI.QnCovLin → PI.QnCovDet :=
  PI.QnCovDetW.qnCovDet_of_lin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
section
theorem covariant_hat_of_lin : PI.QnCovLin → PI.QnCovHat :=
  PI.QnCovHatW.qnCovHat_of_lin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
section
theorem covariant_linear : PI.QnCovLin :=
  PI.QnCovLinW.qnCovLin
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
section
theorem qnEabPres : Formalism.FourierDecayAlt.Q.EabPres := by
  intro E _ _ k r z i D a b f f₂ s hD hf hf₂
  refine ⟨Formalism.FourierDecayAlt.Q.EabLie.eab_smooth i D a b f hf, fun _ hL => ?_, fun g hg => ?_⟩
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_left i z D hD a b f hf hL
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevTransfer
section
theorem level_transfer_of_levHom : Formalism.QuantumDeterminants.LevHom → Formalism.FourierDecayAlt.Q.LevelTransfer := by
  open PIQnLT Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q in
  intro hL E _ _ k i r' z z' Y p q f g hg
  have hinv : (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ := ιLev_inv hL g (isUnit_det_of_UH g hg)
  have hm := mdim_lev k i r'
  have hP : ∀ j, posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast hm j)) :=
    posL_lev k i r'
  have hx : ∀ j, xv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xv]
    rw [fvec_lift, hP, liftVec_lev]
  have hxb : ∀ j, xbv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j =
      xbv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xbv]
    rw [fvec_lift, hP, bvec_lev, herm_liftVec]
  have hy : ∀ j, yv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      yv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [yv]
    rw [hinv, fvec_lift, mulVec_liftVec, hP, liftVec_lev]
  have hyb : ∀ j, ybv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      ybv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [ybv]
    rw [fvec_lift, hP, bvec_lev, mulVec_liftVec, herm_liftVec]
  have hu := uC_lev k i r' Y
  fin_cases p <;> fin_cases q
  · simp only [tL, capL]
    rw [hu]
    exact capL_cast hL hm _ _ hP _ f g
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hx j) (fun j => hyb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hy j) (fun j => hxb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact second_capelli_minor_cast hL hm _ _ hP _ _ _ _ _ _ _ _ _ f g (fun j => hy j) (fun j => hx j)
      (fun j => hyb j) (fun j => hxb j)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleRight
section
theorem qnRuleRight : Formalism.FourierDecayAlt.Q.RuleRight := Formalism.FourierDecayAlt.Q.QRR.ruleRight_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleTorus
section
theorem qnRuleTorus : Formalism.FourierDecayAlt.Q.RuleTorus := by
  open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in
  intro E _ _ k r l D f hD hf c hc g₁ hg₁ hmem
  have hcl : c l ≠ 0 := hc l
  have h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ) := by simp
  have h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    simp
  have h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ)) := by simp
  set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ
  set L := fderiv ℝ φ c with hL
  refine ⟨?_, ?_⟩
  · simp only [EH, EabH]
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pOp, wirt, if_pos hc]
    rw [lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
  · simp only [EH, EabH]
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pbOp, wirtBar, if_pos hc]
    rw [lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnYLeibniz
section
theorem qnYLeibniz : Formalism.FourierDecayAlt.Q.YLeibniz := QnYLeibnizW.y_operator_leibniz_rule
end

