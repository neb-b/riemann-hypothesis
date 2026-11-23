module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.RepCountCongruenceInvariant
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.IsoPeel
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicFiniteOrder.Assembly
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.MemOrdR
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalResidueCharacter.ResCharEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientIntegralBound.QuotientLIntegralLeMultiplicityLIntegral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuarticIndependence.QmIndep
public import Formalism.PeriodIntegrals.Bundle0015
public import Formalism.YangianSpanCharacter.YangianRTTProofs.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EntrywiseSandwichCommute.BlockEmbeddingMulEntrySwap
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.SelfDualLocOfLocBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SigmaStarUniqOf
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.SqPairGlueMain

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert
section
theorem density_exact_inert : Formalism.L2.SG.DensExact.DensExactInert :=
  DensInertW.densExactInert_of DensInertW.hermitianDiagonalization DensInertW.repCountCongruenceInvariant
    DensInertW.anisotropic_valuation_peel DensInertW.isotropic_valuation_peel DensInertW.quadraticDifferenceArith
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdAd
section
theorem finite_order_adelic : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdealLattice
section
theorem ideal_lattice_basis : PI.IdealLattice :=
  PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocHaarRR
section
theorem local_haar_real_real : PI.LocHaarRR.Target := PI.LocHaarRRW.target
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocalEnd
section
theorem local_endomorphism_homeomorph : PI.LocalEndHomeo :=
  PI.LocalEndW.localEndHomeo_of_three PI.LocalEndW.henselRoot PI.LocalEndW.intOfHensel PI.LocalEndW.valOfInt
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PinHostLoc
section
theorem prime_quotient_unit : PI.PinHostLoc.Target := by
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres := PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq p (hg i) hin
  have hi0 : ((g i : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (hg i).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact PI.PinHostLoc.UnitaryGroupMassFormula.irr A (hg i).ne_zero hin hnot
  · obtain ⟨j, hgij, hj⟩ : ∃ j : Fin 2, g i ≠ g j ∧
        ((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F) = ((g j : ℕ) : F) := by
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · exact ⟨1, hne, mul_div_cancel_left₀ _ hi0⟩
      · exact ⟨0, hne.symm, mul_div_cancel_right₀ _ hi0⟩
    have hjp : ((g j : ℕ) : NumberField.RingOfIntegers F) ∉ p.asIdeal := by
      intro hjin
      have hcop : IsCoprime ((g i : ℕ) : ℤ) ((g j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hg i) (hg j)).mpr hgij)
      obtain ⟨a, b, hab⟩ := hcop
      have h1 : (1 : NumberField.RingOfIntegers F) ∈ p.asIdeal := by
        have h2 := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers F) hab
        push_cast at h2
        rw [← h2]
        exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hin) (p.asIdeal.mul_mem_left _ hjin)
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨u, hu, hu'⟩ := PI.PinHostLoc.UnitaryGroupMassFormula.unit A hjp
    exact ⟨u, hu, by rw [hu', hj]⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesFinite
section
theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmIndep
section
theorem rtt_independence' : PI.RTTIndependence := PI.QmIndepW.qmIndep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSandwich
section
private theorem rtt_commutator_sandwich_eq_of_relations {M : Type} [Ring M] (R e2b e1b' e1q' e2q e1a' e2a : M)
    (h1 : e2q * e1a' = e1a' * e2q) (h2 : e2b * e1q' = e1q' * e2b) (h3 : e2b * e1a' = e1a' * e2b)
    (h4 : e2a * e1b' = e1b' * e2a) (h5 : e2q * e1b' = e1b' * e2q) (h6 : e2a * e1q' = e1q' * e2a)
    (hP : R * e1b' * e2b = e2b * e1b' * R) (hU : R * e1a' * e2a = e2a * e1a' * R) :
    e2b * e1b' * (R * e1q' * e2q - e2q * e1q' * R) * (e1a' * e2a) =
      R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) - e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by
  rw [mul_sub, sub_mul]
  congr 1
  · calc e2b * e1b' * (R * e1q' * e2q) * (e1a' * e2a)
        = e2b * e1b' * R * e1q' * (e2q * e1a') * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e2b * e1q' * (e1a' * e2q) * e2a := by rw [← hP, h1]
      _ = R * e1b' * (e2b * e1q') * e1a' * e2q * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e1q' * (e2b * e1a') * e2q * e2a := by rw [h2]; simp only [mul_assoc]
      _ = R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) := by rw [h3]; simp only [mul_assoc]
  · calc e2b * e1b' * (e2q * e1q' * R) * (e1a' * e2a)
        = e2b * e1b' * e2q * e1q' * (R * e1a' * e2a) := by simp only [mul_assoc]
      _ = e2b * e1b' * e2q * e1q' * (e2a * e1a' * R) := by rw [hU]
      _ = e2b * (e1b' * e2q) * (e1q' * e2a) * e1a' * R := by simp only [mul_assoc]
      _ = e2b * (e2q * e1b') * (e2a * e1q') * e1a' * R := by rw [← h5, ← h6]
      _ = e2b * e2q * (e1b' * e2a) * e1q' * e1a' * R := by simp only [mul_assoc]
      _ = e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by rw [← h4]; simp only [mul_assoc]

theorem rtt_sandwich' : PI.RTTSandwich := by
  intro A _ _ QQ p c ci p' c' ci' hW hW' hcomm hQ Y Y'
  dsimp only
  have hbu : ∀ (y : ℂ) (i j : Fin 2), ∀ u ∈ ({p, c, ci} : Set A), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) u := by
    intro y i j u hu
    exact PI.QmSandwichWork.tm_entry_comm y (hcomm u hu p' (by simp)).symm (hcomm u hu c' (by simp)).symm
      (hcomm u hu ci' (by simp)).symm i j
  have hab : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (Formalism.YangianSpanCharacter.T.Tm y' p' c' ci' k l) := by
    intro y y' i j k l
    exact PI.QmSandwichWork.tm_entry_comm y (hbu y' k l p (by simp)).symm (hbu y' k l c (by simp)).symm
      (hbu y' k l ci (by simp)).symm i j
  have haq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p (by simp) y' k l) (hQ c (by simp) y' k l)
      (hQ ci (by simp) y' k l) i j
  have hbq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p' (by simp) y' k l) (hQ c' (by simp) y' k l)
      (hQ ci' (by simp) y' k l) i j
  have h1 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => haq Y' Y i j k l).symm
  have h2 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hbq Y Y' k l i j).symm).symm
  have h3 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hab Y' Y i j k l).symm
  have h4 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hab Y Y' k l i j).symm).symm
  have h5 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hbq Y' Y i j k l).symm
  have h6 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (haq Y Y' k l i j).symm).symm
  have hP : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p' c' ci' Y Y' hW'
  have hU : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' hW
  have hmat := rtt_commutator_sandwich_eq_of_relations _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 hP hU
  change _ = (Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
    (_ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) *
    (Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci))) (0, 0) (0, 0)
  rw [hmat, Matrix.sub_apply, PI.QmSandwichWork.flip_row, PI.QmSandwichWork.flip_col, ← Formalism.FourierDecayAlt.P.W.first_embedding_mul,
    ← Formalism.FourierDecayAlt.P.W.first_embedding_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, PI.QmSandwichWork.block_embedding_mul_entry,
    PI.QmSandwichWork.block_embedding_mul_entry_swap, mul_sub]
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
section
theorem self_dual_local : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
section
theorem sigma_star_unique : PI.SigmaStarUniq := PI.SSU.sigmaStarUniq_of area_lattice_formula
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqPairGlue
section
theorem square_pair_glue : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen :=
  PI.SqPairW.sqPairGlue_main
end

