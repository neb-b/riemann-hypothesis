module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SeesawSumTarget

variable {D : D7}

theorem isHeckeChar_mul {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((χ * η : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => χ x * η x := by
      funext x; simp
    rw [this]
    exact hχ.1.mul hη.1
  · simp only [MonoidHom.mul_apply, hχ.2 x, hη.2 x, mul_one]

theorem exists_scalar {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := _root_.GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, GlobalTheory.WeilUniq.om_om_inv, map_smul] at this

section Std
open GlobalTheory.MixModel

theorem qA_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qA = (fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) 0).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qA, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A)]
  · simp only [fromCols_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem qB_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qB = (fromCols (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E) 1).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qB, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp only [fromCols_apply_inr]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det B)]

theorem pA_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pA ⬝ x = topR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pA, rat, qA_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, topR]
  simp [apply_ite (incA D)]

theorem pB_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pB ⬝ x = botR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pB, rat, qB_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply, botR]
  simp [apply_ite (incA D)]

theorem boxT_sumDec (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    (GlobalTheory.BiTransfer.sumDec A B).boxT S φ φ' = box2 φ φ' := by
  funext x
  simp only [OrthDec.boxT, OrthDec.resT_apply, box2]
  rw [pA_sumDec, pB_sumDec]

theorem emb_sumDec (A B : HSp D) (g : GA D A) (g₁ : GA D B) :
    (GlobalTheory.BiTransfer.sumDec A B).emb (g, g₁) = GlobalTheory.SquareComm.blk A B (g, g₁) := by
  apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum A B)
  rw [(GlobalTheory.BiTransfer.sumDec A B).mt_emb, GlobalTheory.SquareComm.mt_blk]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.Doubling.blkMat, submatrix_apply, Equiv.symm_apply_apply, Matrix.add_apply, Matrix.mul_apply,
    OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, qA_sumDec, qB_sumDec, Matrix.map_apply, id]
  simp only [GlobalTheory.BiTransfer.sumDec, submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> rcases t with t | t <;>
    simp [Matrix.one_apply, apply_ite (incA D), ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

end Std

theorem seesaw_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  intro D ψ hψ S A B χ₁ χ₁' χ₂ χ₂' ω₁ ω₂ H₁ H₂
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨ω₂', H₂'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S B χ₁ χ₂' hη H₁.hecS H₂.hecT H₁.resS H₂.resT
  obtain ⟨ω, H⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.Doubling.hsum A B) χ₁ (χ₁' * χ₂') hη H₁.hecS
    (isHeckeChar_mul H₁.hecT H₂.hecT) H₁.resS (resEta_mul H₁.resT H₂.resT)
  choose c hc using fun p => exists_scalar H₂' H₂ p
  refine ⟨ω, χ₁, χ₁' * χ₂', fun u _ g₁ => (c (u, g₁) : ℂ), H, fun u _ g₁ => Circle.norm_coe _,
    fun φ φ' hφ hφ' => ⟨?_, fun u g g₁ => ?_⟩⟩
  · rw [← boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec A B).isThetaFunO_boxT hφ hφ'
  · have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ₁ χ₁' χ₂' ω ω₁
      ω₂' H H₁ H₂' u g g₁ φ φ' hφ hφ'
    simp only [thetaKO]
    rw [← emb_sumDec, ← boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero, hc (u, g₁) φ' hφ', Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.SeesawSumTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGram
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Member.selfDualLat_neg_gram_transpose : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D), GlobalTheory.UCls.SelfDualLat (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) := by
  intro D V
  obtain ⟨-, -, hfg, hsp, -, hcc, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hint : ∀ z : D.host.E, IsIntegral ℤ z ↔
      z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)]
  refine ⟨?_, ?_, hfg, hsp, ?_⟩
  · intro a b
    simp only [Matrix.neg_apply, map_neg, ← hcc, hG]
  · rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  · intro x
    rw [← hL x]
    refine forall_congr' fun y => imp_congr_right fun _ => ?_
    have he : herm (-(V.gram)ᵀ) x y = -(∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) := by
      simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, hcc]
    rw [he, hint, ← hint, ← hint]
    exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectAverageIndicatorLowerBound
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine.LowerAverage

theorem countable_subgroupOf {G : Type} [Group G] (Λ N : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf N) := by
  refine Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : Λ)) ?_
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Λ => (z : G)) h))

theorem right_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (N Λ : Subgroup G) [Countable Λ] (hN : IsClosed (N : Set G)) (ν : Measure N)
    (hν : ν.IsHaarMeasure) (D : Set N) (hD : IsFundamentalDomain (Λ.subgroupOf N) D ν)
    (hfin : ν D ≠ ⊤) : ν.IsMulRightInvariant := by
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set G))
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_subgroupOf Λ N
  exact RightUnfold.isMulRightInvariant_of_lattice ν (Λ.subgroupOf N) D hD hfin

theorem average_lower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ C : Set G, IsCompact C → ∃ (U : Set G) (c : ℝ≥0∞), IsOpen U ∧ μ U ≠ ⊤ ∧ c ≠ 0 ∧ ∀ u₀ ∈ N, ∀ m₀ ∈ M, ∀ y ∈ C, c ≤ ∫⁻ m : M, ∫⁻ u : N, U.indicator 1 ((u : G) * m * (u₀ * m₀ * y)) ∂ν ∂π := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM H μ hμ C hC
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set G))
  haveI : BorelSpace M := Subtype.borelSpace (fun x => x ∈ (M : Set G))
  haveI := H.haarN
  haveI := H.haarM
  haveI := right_of_closed N Λ H.closedN ν H.haarN DN H.domN H.finN
  haveI := right_of_closed M Λ H.closedM π H.haarM DM H.domM H.finM
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  obtain ⟨W, hW, hWC⟩ := compact_open_separated_mul_left hC isOpen_interior hCK
  obtain ⟨V, hVo, hV1, hVW⟩ := exists_open_nhds_one_mul_subset hW
  have hVN : IsOpen ((↑) ⁻¹' V : Set N) := hVo.preimage continuous_subtype_val
  have hVM : IsOpen ((↑) ⁻¹' V : Set M) := hVo.preimage continuous_subtype_val
  refine ⟨interior K, ν ((↑) ⁻¹' V) * π ((↑) ⁻¹' V), isOpen_interior,
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne,
    mul_ne_zero (hVN.measure_ne_zero ν ⟨1, hV1⟩) (hVM.measure_ne_zero π ⟨1, hV1⟩), ?_⟩
  intro u₀ hu₀ m₀ hm₀ y hy
  have h1 : ∀ m : M, ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞) ((u : G) * m * (u₀ * m₀ * y)) ∂ν
      = ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y) ∂ν := by
    intro m
    rw [← lintegral_mul_right_eq_self (fun u : N => (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y)) ⟨m * u₀ * (m : G)⁻¹, H.norm m m.2 u₀ hu₀⟩]
    refine lintegral_congr fun u => ?_
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [h1]
  rw [lintegral_mul_right_eq_self (fun m : M => ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * (m : G) * y) ∂ν) ⟨m₀, hm₀⟩, ← lintegral_indicator_const hVM.measurableSet]
  refine lintegral_mono fun m => ?_
  by_cases hm : m ∈ ((↑) ⁻¹' V : Set M)
  swap
  · rw [Set.indicator_of_notMem hm]
    exact bot_le
  rw [Set.indicator_of_mem hm]
  rw [← lintegral_indicator_one hVN.measurableSet]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ ((↑) ⁻¹' V : Set N)
  swap
  · rw [Set.indicator_of_notMem hu]
    exact bot_le
  rw [Set.indicator_of_mem hu]
  have : (u : G) * m * y ∈ interior K :=
    hWC (Set.mul_mem_mul (hVW (Set.mul_mem_mul hu hm)) hy)
  rw [Set.indicator_of_mem this]
  exact le_rfl

end GlobalTheory.ResLine.LowerAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqOfSetLIntegralEq
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem measure_mul_setLIntegral_eq [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (D : Set X) (hD : MeasurableSet D) (E : Set S)
    (hE : MeasurableSet E) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ :=
  _root_.GlobalTheory.lintegral_mul_measure_inter_smul_preimage S X ν μ D hD E hE ψ hψ hinv

theorem lintegral_unfold_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ :=
  GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure S X ν μ Γ D₁ D₂ hD₁ hD₂ E hE hEf ψ hψ hinv

theorem ae_measure_setOf_smul_mem_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E :=
  GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq S X ν μ Γ D hD hDf E hE

theorem lintegral_mul_eq_of_measurable [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S) (hD₁m : MeasurableSet D₁) (hD₂m : MeasurableSet D₂)
    (hE₂m : MeasurableSet E₂)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  rw [measure_mul_setLIntegral_eq ν μ D₁ hD₁m E₂ hE₂m ψ hψ hinv,
    lintegral_unfold_eq ν μ Γ₂ D₁ D₂ hD₁m hD₂ E₂ hE₂m hE₂ ψ hψ hinv, ← lintegral_const_mul _ hψ]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_measure_setOf_smul_mem_eq ν μ Γ₁ D₁ hD₁m hD₁ E₁ hE₁] with y hy
  have : ν {s : S | s⁻¹ • y ∈ D₁} = ν {s : S | s • y ∈ D₁} := by
    change ν ({s : S | s • y ∈ D₁}⁻¹) = _
    exact Measure.measure_inv (μ := ν) _
  rw [this, hy, mul_comm]
end GlobalTheory.CovolIndep

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem lintegral_mul_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  have a₁ := hD₁.nullMeasurableSet.toMeasurable_ae_eq
  have a₂ := hD₂.nullMeasurableSet.toMeasurable_ae_eq
  have b₂ := hE₂.nullMeasurableSet.toMeasurable_ae_eq
  have key := lintegral_mul_eq_of_measurable ν μ Γ₁ Γ₂ (toMeasurable μ D₁) (toMeasurable μ D₂)
    E₁ (toMeasurable ν E₂) (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _)
    (measurableSet_toMeasurable _ _) (isFundamentalDomain_of_ae_eq hD₁ a₁)
    (isFundamentalDomain_of_ae_eq hD₂ a₂) hE₁ (isFundamentalDomain_of_ae_eq hE₂ b₂) ψ hψ hinv
  rwa [measure_toMeasurable, setLIntegral_congr a₁, setLIntegral_congr a₂] at key

end GlobalTheory.CovolIndep

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ZConvLeft

theorem isThetaFunO_down {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  have h0 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (ρ.vT i j) :=
    (ρ.vT_is t i j i.2.le j.2).2.2
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt W.ψ_std W.θ_is (h1 d' hd').1.2 h0
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf _

theorem kerSmall_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g u, kerSmall W Θ' (γ * g) g₁ u = kerSmall W Θ' g g₁ u := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g u
  have hω := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hth := isThetaFunO_down W B ρ t i j hΘ
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  congr 2
  show thetaKO (W.om (.mu t i j)) u (γ * g) d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
  unfold thetaKO
  have e : ((u, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (u, g) := by simp
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hth d hd))

end GlobalTheory.ZConvLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalities
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.Div.SquareRanks

theorem square_ranks : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (i j : Fin D.R.m),
    (spW₁ G i j).rank < (spW G i j).rank ∧ Even ((spW G i j).rank + (spW₁ G i j).rank) ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < ((spW G i j).rank - (spW₁ G i j).rank) / 2 ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL i j
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  have e3 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  rw [e1, e2, e3]
  have h0 : D.R.r ≤ rankV D i j := by unfold rankV; omega
  have ht := D.R.t_odd
  have hk := D.R.k_even
  have hm := D.R.m_even
  have h3 := D.R.three_m_lt_t
  have h4 := D.R.m_add_three_le_k
  have h5 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = D.R.r + 6 := rfl
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [Nat.even_iff]
  omega

end GlobalTheory.Div.SquareRanks
end

