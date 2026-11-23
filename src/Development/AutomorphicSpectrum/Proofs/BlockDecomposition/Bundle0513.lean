module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBruhatDecomposition
section
noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem inv_block_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) :
    (blk4 A B C D)⁻¹ = blk4 (cT σ D) (-cT σ B) (-cT σ C) (cT σ A) := by
  rw [inv_of_unitary σ h, cT_blk4]
  unfold Jm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, neg_block_matrix]
  congr 1 <;> simp

theorem isotropic_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) : C * cT σ D = D * cT σ C := by
  have h1 : blk4 A B C D * (blk4 A B C D)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_unitary σ h)
  rw [inv_block_of_unitary σ h, submatrix_fromBlocks_mul, ← block_matrix_one] at h1
  have := (blockMatrixTwoByTwoFin_injective h1).2.2.1
  rw [Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
  exact this

theorem repMat_unitary (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) :
    IsUnit (repMat σ b a).det ∧ IsUnitary σ (Jm K n) (repMat σ b a) := by
  have hu : IsUnitary σ (Jm K n) (repMat σ b a) := by
    unfold repMat
    refine unitary_mul σ (unitary_mul σ ?_ ?_) ?_
    · unfold IsUnitary wr Jm
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      have e2 := eId_mul_eId (K := K) n r
      simp only [cT_sub, cT_one, cT_neg, cT_eId]
      congr 1
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
    · unfold IsUnitary nB Jm
      have hB : cT σ (extB (n := n) b) = extB b := by rw [cT_extB, hb]
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      simp [cT_one, cT_zero, hB]
    · unfold IsUnitary mA Jm
      have ha' := isUnit_det_cT σ ha
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, cT_inv σ ha', cT_cT σ hσ]
      simp [cT_zero, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]
  exact ⟨isUnit_det_of_unitary σ hu, hu⟩

theorem siegel_rep_iff (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) (A B C D : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 A B C D * (repMat σ b a)⁻¹) ↔
      C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  have hu := (repMat_unitary σ hσ b a hb ha).2
  rw [repMat_eq] at hu ⊢
  rw [inv_block_of_unitary σ hu, submatrix_fromBlocks_mul, is_siegel_parabolic_block_iff]
  simp only [cT_mul, cT_neg, cT_sub, cT_one, cT_eId, cT_extB, hb, cT_inv σ (isUnit_det_cT σ ha), cT_cT σ hσ,
    neg_neg, Matrix.mul_neg, Matrix.mul_assoc]

theorem factor_of_siegel {n : ℕ} {g h : Matrix (Fin (n + n)) (Fin (n + n)) K} (hg : IsUnit g.det)
    (hh : IsUnit h.det) (hp : IsSiegelP (g * h⁻¹)) {A B C D A' B' C' D' : Matrix (Fin n) (Fin n) K}
    (eg : g = blk4 A B C D) (eh : h = blk4 A' B' C' D') :
    ∃ p : Matrix (Fin n) (Fin n) K, IsUnit p.det ∧ C = p * C' ∧ D = p * D' := by
  obtain ⟨p1, p2, p3, p4, hp'⟩ := exists_blockMatrixTwoByTwoFin_eq (g * h⁻¹)
  rw [hp', is_siegel_parabolic_block_iff] at hp
  subst hp
  have hgp : g = blk4 p1 p2 0 p4 * h := by
    rw [← hp', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.mul_one]
  have hdet : IsUnit (blk4 p1 p2 0 p4).det := by
    rw [← hp', Matrix.det_mul]; exact hg.mul (Matrix.isUnit_nonsing_inv_det _ hh)
  rw [det_block_lower_zero] at hdet
  rw [eg, eh, submatrix_fromBlocks_mul] at hgp
  have := blockMatrixTwoByTwoFin_injective hgp
  refine ⟨p4, isUnit_of_mul_isUnit_right hdet, ?_, ?_⟩
  · simpa using this.2.2.1
  · simpa using this.2.2.2

theorem herm_unique (σ : K →+* K) {n r : ℕ} (hr : r ≤ n) (a : Matrix (Fin n) (Fin n) K) (ha : IsUnit a.det)
    (b b' : Matrix (Fin r) (Fin r) K) (p p' : Matrix (Fin n) (Fin n) K) (hp : IsUnit p.det)
    (hC : p * -(eId K n r * a) = p' * -(eId K n r * a))
    (hD : p * ((1 - eId K n r - extB b) * (cT σ a)⁻¹) = p' * ((1 - eId K n r - extB b') * (cT σ a)⁻¹)) :
    b = b' := by
  have ha' := isUnit_det_cT σ ha
  have h1 : p * eId K n r = p' * eId K n r := by
    have := congrArg (· * a⁻¹) hC
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha] using this
  have h2 : p * (1 - eId K n r - extB b) = p' * (1 - eId K n r - extB b') := by
    have := congrArg (· * cT σ a) hD
    simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha'] using this
  have key : ∀ b₀ : Matrix (Fin r) (Fin r) K,
      (1 - eId K n r - extB b₀) * (1 - eId K n r) = 1 - eId K n r := by
    intro b₀
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, eId_mul_eId, extB_mul_eId]
    abel
  have h3 : p * (1 - eId K n r) = p' * (1 - eId K n r) := by
    calc p * (1 - eId K n r) = p * ((1 - eId K n r - extB b) * (1 - eId K n r)) := by rw [key]
      _ = p * (1 - eId K n r - extB b) * (1 - eId K n r) := by rw [Matrix.mul_assoc]
      _ = p' * (1 - eId K n r - extB b') * (1 - eId K n r) := by rw [h2]
      _ = p' * (1 - eId K n r) := by rw [Matrix.mul_assoc, key]
  have hpp : p = p' := by
    have e1 : ∀ q : Matrix (Fin n) (Fin n) K, q = q * eId K n r + q * (1 - eId K n r) := by
      intro q; rw [← Matrix.mul_add]; simp
    rw [e1 p, e1 p', h1, h3]
  subst hpp
  have := congrArg (p⁻¹ * ·) h2
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul, sub_right_inj] at this
  exact extB_injective hr this

theorem bruhat : Bruhat := by
  intro K _ σ hσ _ n c hc a ha
  have hr : ∀ U : Submodule K (Fin n → K), Module.finrank K U ≤ n := fun U =>
    (Submodule.finrank_le U).trans (by simp)
  refine ⟨fun U b hb => repMat_unitary σ hσ b (a U) hb (ha U).1, ?_⟩
  intro g hg hgu
  obtain ⟨A, B, C, D, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq g
  have hiso := isotropic_of_unitary σ hgu
  set U := Submodule.span K (Set.range C) with hU
  obtain ⟨T, L, hT, -, hLT⟩ := GlobalTheory.T.same_span_transfer_matrices C (c U) (hc U).1 (hc U).2
  obtain ⟨b, hb, hcond⟩ := _root_.GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft σ hσ (hr U) (c U) (a U) C D T L (ha U) hT hLT hiso
  have hS := (siegel_rep_iff σ hσ b (a U) hb (ha U).1 A B C D).2 hcond
  refine ⟨⟨U, b, hb⟩, hS, ?_⟩
  rintro ⟨U', b', hb'⟩ hq
  have hrep' := repMat_unitary σ hσ b' (a U') hb' (ha U').1
  obtain ⟨p', hp', hC', hD'⟩ := factor_of_siegel hg hrep'.1 hq rfl (repMat_eq σ b' (a U'))
  have hUU : U' = U := by
    rw [← (hc U').2, ← _root_.GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft (hr U') (c U') (a U') p' (ha U') hp', ← hC']
  subst hUU
  have hrep := repMat_unitary σ hσ b (a U) hb (ha U).1
  obtain ⟨p, hp, hC, hD⟩ := factor_of_siegel hg hrep.1 hS rfl (repMat_eq σ b (a U))
  have hbb := herm_unique σ (hr U) (a U) (ha U).1 b' b p' p hp' (hC'.symm.trans hC) (hD'.symm.trans hD)
  subst hbb
  rfl

end GlobalTheory.CompanionTheory.BruhatCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandard
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.Euler

theorem pureN_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureN φ A X = {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v}.indicator
        (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) X := by
  change φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
    (boxF A).indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) = _
  by_cases hX : ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∈ boxF A := hX
    rw [Set.indicator_of_mem (show X ∈ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_mem h1, mul_one]
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∉ boxF A := hX
    rw [Set.indicator_of_notMem (show X ∉ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_notMem h1, mul_zero]

theorem integrable_integral_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ M n d b I c minf m hE
  obtain ⟨-, -, S₀, hS₀⟩ := hE
  refine ⟨S₀, fun S hS φ hφ hφi A hA hfin hoff => ?_⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hB := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurableSet_box b n M S A hA hoff
  have hp := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurable_projInf (E := E) b n M
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) :=
    {X | ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} with hBdef
  set P : ℝ := ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal with hP
  have hP0 : 0 ≤ P := tprod_nonneg fun _ => ENNReal.toReal_nonneg
  set K : ℝ≥0∞ := (c : ℝ≥0∞) * (∏ v ∈ S, m v (A v)) * ENNReal.ofReal P with hK
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.prod_ne_top fun v _ => hfin v)) ENNReal.ofReal_ne_top
  have hmap : (I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf = K • minf := by
    ext T hT
    rw [Measure.map_apply hp hT, Measure.restrict_apply (hp hT), Measure.smul_apply, smul_eq_mul]
    have hform := hS₀ S hS (T.indicator 1) (fun v => (A v).indicator 1)
      (measurable_one.indicator hT) (fun v => measurable_one.indicator (hA v))
    simp_rw [GlobalTheory.CompanionTheory.SW.EulerBox.pureL_indicator_eq b S _ A hoff] at hform
    rw [lintegral_indicator hB, lintegral_indicator_one hT] at hform
    have hl : ∫⁻ X in B, T.indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) ∂I =
        I (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T ∩ B) := by
      have : (fun X => T.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) =
          (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T).indicator 1 := by
        funext X
        by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projInf X ∈ T
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show X ∈ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
          rfl
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show X ∉ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
      rw [this, lintegral_indicator_one (hp hT), Measure.restrict_apply (hp hT)]
    rw [hl] at hform
    change _ = _ * _ * ENNReal.ofReal P at hform
    rw [hform]
    simp_rw [lintegral_indicator_one (hA _)]
    rw [hK]; ring
  have hfun : pureN φ A = B.indicator (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) :=
    funext fun X => pureN_eq_indicator φ A X
  refine ⟨?_, ?_⟩
  · have h1 : Integrable φ ((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [hmap]; exact hφi.smul_measure hKtop
    have h2 := (integrable_map_measure hφ.aestronglyMeasurable hp.aemeasurable).1 h1
    rw [hfun]
    exact IntegrableOn.integrable_indicator h2 hB
  · have h1 : ∫ X, pureN φ A X ∂I = ∫ Y, φ Y ∂((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [integral_map hp.aemeasurable hφ.aestronglyMeasurable, hfun]
      exact integral_indicator hB
    rw [h1, hmap, integral_smul_measure]
    have hKr : K.toReal = (c : ℝ) * (∏ v ∈ S, (m v (A v)).toReal) * P := by
      rw [hK, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal hP0]
      simp
    rw [hKr, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WhitFree.Euler
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

def petersson {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a)
    (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) :
    π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun φ ψ => inner ℂ (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ))
    (fun φ φ' ψ => by simp only [map_add (f := _), inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun φ ψ ψ' => by simp only [map_add (f := _), inner_add_left])
    (fun c φ ψ => by simp only [map_smul, inner_smul_left, smul_eq_mul])

theorem exists_isHerm : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  intro hB E _ _ _ a μ _ _ π hπ
  have hl := _root_.GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised hB E a μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have hb : ∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := fun φ hφ => (hl φ hφ).2
  refine ⟨petersson μ π hm, fun X φ ψ => _root_.GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint E a μ π hm hb X φ ψ, ?_⟩
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have hi : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π.cusp ψ hψ).1.level
  have hT : toL2ₗ μ π.V hm ⟨φ, hφ⟩ ≠ 0 := fun h =>
    hne (congrArg Subtype.val (hi (h.trans (map_zero _).symm)))
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show inner ℂ (toL2ₗ μ π.V hm ⟨φ, hφ⟩) (toL2ₗ μ π.V hm ⟨φ, hφ⟩) ≠ 0
  exact inner_self_ne_zero.2 hT

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

namespace PureTuple

open NumberField IsDedekindDomain
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem coord_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    PureSB.coordH (Fv F v) b (projV v X a i) k = (PureSB.coordH (Af F) b (X a i) k) v :=
  PureSB.repr_map b (evalV F v) (X a i) k

theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → Fin n → Fin M → Fv F v ⊗[F] E) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  have h : (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X a i) = fun X =>
      (PureSB.coordH (Fv F v) b).symm (fun k => (PureSB.coordH (Af F) b (X a i) k) v) := by
    funext X
    apply (PureSB.coordH (Fv F v) b).injective
    rw [Homeomorph.apply_symm_apply]
    funext k
    exact coord_projV v b X a i k
  rw [h]
  refine (PureSB.coordH (Fv F v) b).symm.continuous.comp (continuous_pi fun k => ?_)
  exact (RestrictedProduct.continuous_eval v).comp ((continuous_apply k).comp
    ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))

theorem projV_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ latV b v ↔ ∀ a i k, (PureSB.coordH (Af F) b (X a i) k) v ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun a => forall_congr' fun i => forall_congr' fun k => ?_
  rw [← coord_projV v b X a i k]
  rfl

variable {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))


include b in
theorem isClosed_boxF (hA : ∀ v, IsCompact (A v)) : IsClosed (boxF A) := by
  have h : boxF A = ⋂ v, projV v ⁻¹' A v := by
    ext X
    exact ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
  rw [h]
  refine isClosed_iInter fun v => ?_
  haveI : T2Space (Fv F v ⊗[F] E) := (PureSB.coordH (Fv F v) b).isEmbedding.t2Space
  exact (hA v).isClosed.preimage (continuous_projV v b)

theorem isOpen_boxF (hA : ∀ v, IsOpen (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) : IsOpen (boxF A) := by
  have hT : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have hI : IsOpen {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} := by
    have e : {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
        PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} =
        ⋂ a, ⋂ i, ⋂ k, (fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k) ⁻¹'
          {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k :=
      (continuous_apply k).comp
        ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))
    exact hT.preimage hc
  have h : boxF A = {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} ∩
      ⋂ v ∈ S, projV v ⁻¹' A v := by
    ext X
    constructor
    · intro hX
      refine ⟨fun a i k v hv => ?_, Set.mem_iInter₂.2 fun v _ => hX v⟩
      have := hX v
      rw [hS v hv] at this
      exact (projV_mem_latV v b X).1 this a i k
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact Set.mem_iInter₂.1 h2 v hv
      · rw [hS v hv]
        exact (projV_mem_latV v b X).2 fun a i k => h1 a i k v hv
  rw [h]
  exact hI.inter (isOpen_biInter_finset fun v _ => (hA v).preimage (continuous_projV v b))

theorem isCompact_boxF (hA : ∀ v, IsCompact (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    IsCompact (boxF A) := by
  let B : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun a i k v => (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => PureSB.coordH (Fv F v) b (Y a i) k) '' A v
  have hB : ∀ a i k v, IsCompact (B a i k v) := fun a i k v =>
    (hA v).image ((continuous_apply k).comp
      ((PureSB.coordH (Fv F v) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))
  have hBS : ∀ a i k v, v ∉ S →
      B a i k v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro a i k v hv _ ⟨Y, hY, rfl⟩
    rw [hS v hv] at hY
    exact hY a i k
  let eW : (Fin n → Fin M → Af F ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Af F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => PureSB.coordH (Af F) b
  have hL : IsCompact (eW ⁻¹' Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k =>
      {y : Af F | ∀ v, y v ∈ B a i k v}) :=
    eW.isCompact_preimage.2 (isCompact_univ_pi fun a => isCompact_univ_pi fun i =>
      isCompact_univ_pi fun k => PureSB.isCompact_box S (B a i k) (hB a i k) (hBS a i k))
  refine hL.of_isClosed_subset (isClosed_boxF b A hA) fun X hX a _ i _ k _ v => ?_
  exact ⟨projV v X, hX v, coord_projV v b X a i k⟩

end PureTuple

theorem pureN_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b S φ A hφ hA hS
  have hc := PureTuple.isCompact_boxF b S A (fun v => (hA v).1) hS
  have hcl := PureTuple.isClosed_boxF b A fun v => (hA v).1
  have ho := PureTuple.isOpen_boxF b S A (fun v => (hA v).2) hS
  refine GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod hφ (Φf := (boxF A).indicator fun _ => (1 : ℂ)) ⟨?_, ?_⟩ fun _ => rfl
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hcl, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro' hc hcl fun Y hY => Set.indicator_of_notMem hY _

end GlobalTheory.CompanionTheory.WhitFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CjEx

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjAbove {v : PlF E} (w : Above v) : Above v :=
  ⟨conjSrc (IsCMField.complexConj E).toRingEquiv w.1,
    (GlobalTheory.DefU.LocRet.under_conjSrc (E := E) w.1).trans w.2⟩

def cj (v : PlF E) : Av v →+* Av v :=
  RingHom.pi fun w => (conjLoc (IsCMField.complexConj E).toRingEquiv w.1 : _ →+* _).comp
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

theorem continuous_cj (v : PlF E) : Continuous (cj v) :=
  continuous_pi fun w => (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w.1).1.comp (continuous_apply (conjAbove w))

theorem projv_conjFin (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj v (projv v x) :=
  funext fun _ => pLoc_conjFin _ _ _

end GlobalTheory.CompanionTheory.CjEx

theorem GlobalTheory.CompanionTheory.CjEx.cjEx : PositivityTheory.Rg.BcB.G8.Fin.CjEx := fun _ _ _ _ v =>
  ⟨GlobalTheory.CompanionTheory.CjEx.cj v, GlobalTheory.CompanionTheory.CjEx.continuous_cj v, GlobalTheory.CompanionTheory.CjEx.projv_conjFin v⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamilyStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_minimal_commutes_projection_family : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, ∀ k, (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.LeviComm.leviMin_comm_projFam | exact GlobalTheory.CompanionTheory.ParCocompact.LeviComm.leviMin_comm_projFam | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.LeviComm.leviMin_comm_projFam <;> assumption)
end

