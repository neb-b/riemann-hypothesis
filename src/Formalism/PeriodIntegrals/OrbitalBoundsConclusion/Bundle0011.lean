module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BallQuotientLength.LengthBallQuotientEqSumMulFdeg
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarScaling.MapEqSelfOfIterate
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.FoldDCUnfoldOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.Bundle0001
public import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOfSpan
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.CmpSplit
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeSaturation.LocLatSat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.LocOProjOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiTorsionFree.Lattice
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OpBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BallQuotLen
section
theorem ball_quotient_length : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CdHaarScale
section
open MeasureTheory MeasureTheory.Measure PI.UnitaryGroupMassFormula.CdHaarScale.Main

theorem cd_haar_scaling : PI.CdHaarScale := by
  intro cd n ε
  by_cases hex : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false)
  · obtain ⟨P₀, Q₀, e₀, h1₀, h2₀⟩ := hex
    have key : ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
        (h2 : ∀ j, ε (e (Sum.inr j)) = false),
        (cd.cd P Q).map (phi e h1 h2) = (cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀) := by
      intro P Q e h1 h2
      have hP : P = P₀ := (card_true e h1 h2).symm.trans (card_true e₀ h1₀ h2₀)
      have hQ : Q = Q₀ := (card_false e h1 h2).symm.trans (card_false e₀ h1₀ h2₀)
      subst hP hQ
      have := cd.haar P Q
      exact map_phi_indep e₀ e h1₀ h2₀ h1 h2 (cd.cd P Q)
    have := cd.haar P₀ Q₀
    have hν : (cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀) =
        haarScalarFactor ((cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀)) (Formalism.REAL.muG ε) • Formalism.REAL.muG ε :=
      isMulLeftInvariant_eq_smul _ _
    refine ⟨haarScalarFactor ((cd.cd P₀ Q₀).map (phi e₀ h1₀ h2₀)) (Formalism.REAL.muG ε),
      haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
    intro P Q e h1 h2 A hA
    have hp : Measurable (⇑(phi e h1 h2)) := (phi e h1 h2).continuous.measurable
    rw [tie_set e h1 h2 A, ← Measure.map_apply hp hA, key P Q e h1 h2]
    conv_rhs => rw [hν]
    rw [ENNReal.smul_def]
  · refine ⟨1, one_pos, ?_⟩
    intro P Q e h1 h2
    exact absurd ⟨P, Q, e, h1, h2⟩ hex
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldDCUnfold
section
theorem fold_dc_unfold : PI.FoldDCUnfold.FoldDCUnfold :=
  PI.FoldDCUnfold.W.foldDCUnfold_of PI.FoldDCUnfold.W.translation_exists
    PI.FoldDCUnfold.W.translation_independent PI.FoldDCUnfold.W.translation_product
    PI.FoldDCUnfold.W.double_coset_translation lintegralTransversalSum
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GenFrameSB
section
theorem coeffNormLE_iff_spanNormLE_of_hasCompl : CutKW.KWsb := GenFrameSpan.genFrameSB_of_span GenFrameSpan.stepSpan
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HeckeProd
section
theorem hecke_product_rule : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), χ.ProductRule :=
  fun _ _ _ χ => PI.HeckeProdW.productRule χ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocCartanPair
section
theorem local_cartan_pair : PI.SqPair.LocCartanPair :=
  PI.SqPair.LCP.locCartanPair_of PI.SqPair.LCP.pair_dichotomy PI.SqPair.LCP.base_lagrangian
    (PI.SqPair.LCP.step_of PI.SqPair.LCP.pair_selection PI.SqPair.LCP.hyperbolic_plane
      PI.SqPair.LCP.pair_split')
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocLatSat
section
theorem inf_eq_inter_span : PI.LocLatSat.Stmt := PI.LocLatSat.UnitaryGroupMassFormula.locLatSat
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj
section
theorem projectiveOverOrder : PI.LocHerm.LocOProj :=
  PI.LocHerm.OProj.locOProj_of PI.LocHerm.OProj.sqCase PI.LocHerm.OProj.nonSqCase
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinkowskiQ
section
theorem minkowski_bound_rat : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OddDualWeyl
section
theorem oddDualWeyl {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    PI.OddDualWeyl.OddFact (K := K) O m lam :=
  PI.OddDualWeyl.odd_dual_weyl_factorization O m lam
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OpWords
section
theorem operator_words_bound : Formalism.MainNotions.TestSideCounting.OpBound :=
  PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhGram
section
theorem phase_gram' : PI.FglGram.PhGram :=
  PI.UnitaryGroupMassFormula.PhGram.phGram_of_steps PI.UnitaryGroupMassFormula.PhGram.gram_bilinear_expansion PI.UnitaryGroupMassFormula.PhGram.gram_sum_first_variable
end

