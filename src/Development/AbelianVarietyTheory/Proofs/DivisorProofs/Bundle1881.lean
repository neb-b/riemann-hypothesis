module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
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
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.BergComp

open MeasureTheory

theorem bergOn_le_supConst : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 → ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) → ∀ (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z → AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) := by
  intro hT D j H Dw l Xo c U dict hL σ hσ G hG w hw hsp Z y hy
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  set A := AllWt.framesOn (U σ) Z with hA
  set S : Set (U σ).Comp := {k | ∃ f, (⟨k, f⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ A} with hS
  have key : ∀ g, dict σ g ∈ A ↔ (dict σ g).1 ∈ S := fun g =>
    ⟨fun h => ⟨_, h⟩, fun ⟨f, hf⟩ =>
      GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ f _ (hdom g) hf⟩
  set la := AllWt.modelWt (U σ) G with hla
  have hchi := GlobalTheory.AllWt.Model.chi_modelWt (U σ) (hL.chiTriv σ hσ) G hG
  set Cl := AllWt.classesOver (D.sp.W j) (dict σ) A with hCl
  have hyS : y.1 ∈ S := ⟨y.2.1, hy⟩
  unfold AllWt.bergOn AllWt.bergE
  refine iSup₂_le fun P hP => ?_
  set P' : Formalism.L2.Pj.FDSec (U σ).X := fun k => if k ∈ S then P k else 0 with hP'
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := by
    refine Formalism.L2.Pj.holCusp_mem_holSub _ _ fun k => ?_
    by_cases hk : k ∈ S
    · simp only [hP', if_pos hk]
      exact Formalism.L2.Pj.holSub_comp_SS _ _ _ hP k
    · simp only [hP', if_neg hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hpt : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r,
      AllWt.ptN la P' z = if z.1 ∈ S then AllWt.ptN la P z else 0 := fun z => by
    by_cases hz : z.1 ∈ S
    · simp only [AllWt.ptN, hP', if_pos hz]
    · simp only [AllWt.ptN, hP', if_neg hz]
      exact Formalism.L2.Pj.pnorm_zero _ _ _

  have h1 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤ Formalism.L2.Pj.supE (U σ).X la P' ^ 2 := by
    have e : AllWt.ptN la P ⟨y.1, y.2.1⟩ = AllWt.ptN la P' ⟨y.1, y.2.1⟩ := by
      rw [hpt, if_pos hyS]
    rw [e]
    gcongr
    exact le_iSup (fun p : Formalism.L2.Pj.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P' p.1) p.2)) y

  have h2 := _root_.GlobalTheory.supPetersson_of_tamagawa hT D j H Dw l Xo c U dict hL σ hσ la w hw hsp hchi P' hP'm

  have h3 : AllWt.petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P' ≤
      AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P := by
    have hsupp : Function.support (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) ⊆ Cl := by
      intro q hq
      by_contra hn
      apply hq
      have : ¬ (dict σ q.out).1 ∈ S := fun h => hn ((key _).2 h)
      show AllWt.ptN la P' (dict σ q.out) = 0
      rw [hpt, if_neg this]
    unfold AllWt.petE
    have hrestrict : eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2
        ((muQ1 (D.sp.W j)).restrict Cl) =
        eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2 (muQ1 (D.sp.W j)) := by
      simp only [eLpNorm'_eq_lintegral_eNorm]
      congr 1
      apply setLIntegral_eq_of_support_subset
      simpa using hsupp
    rw [← hrestrict]
    calc eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2 ((muQ1 (D.sp.W j)).restrict Cl)
        ≤ eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2 ((muQ1 (D.sp.W j)).restrict Cl) := by
          refine eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall fun q => ?_)
          rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), hpt]
          split_ifs
          · exact le_rfl
          · exact AllWt.ptN_nonneg _ _ _
      _ ≤ eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2
            (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) := by
          show _ ≤ eLpNorm' _ 2 ((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl)
          rw [eLpNorm'_smul_measure (by norm_num)]
          refine le_mul_of_one_le_left (by simp) ?_
          exact ENNReal.one_le_rpow (ENNReal.one_le_inv.2 prob_le_one) (by norm_num)
  have h4 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) *
        AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2 :=
    h1.trans (h2.trans (by gcongr))
  exact ENNReal.div_le_of_le_mul h4

end GlobalTheory.BergComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SchurCharV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_ne_zero_Fv (v : Pl (F := F)) : (2 : Fv F v) ≠ 0 := by
  have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
  rwa [map_ofNat, map_zero] at h

theorem eq_liftU_of_UAt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {n : ℕ}
    (X : Spc F E n) (herm : ∀ i j, σ (X.J j i) = algebraMap F E 1 * X.J i j) (hJ : IsUnit (X.J.map t).det)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) :
    g = GlobalTheory.SplitUnitLift.liftU h t X.J 1 herm hJ (Matrix.GeneralLinearGroup.map (piW t) g.1) := by
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  have hv : g'.val = (mat g).map (piW t) := rfl
  set L := GlobalTheory.SplitUnitLift.liftU h t X.J 1 herm hJ g' with hL
  have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have tr : ∀ (A B C : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (Aᵀ * B * C).map (piW t) = (A.map (piW t))ᵀ * B.map (piW t) * C.map (piW t) := fun A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hJm : (incM F X.J).map (piW t) = X.J.map t := by
    unfold incM
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.SplitGLLift.piW_inclR t (X.J i j)
  have hcm : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => GlobalTheory.VacIso.piW_cA σ t _
  have hUt : ((mat g)ᵀ * incM F X.J * (mat g).map (cA σ)).map (piW t) = (incM F X.J).map (piW t) := by rw [hU]
  rw [tr, hJm, hcm, ← hv] at hUt
  set gs := (mat g).map (piW (t.comp σ)) with hgs
  have hσ : gs = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t := by
    have e : gs = ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) := by
      rw [show ((X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ) * ((g'.val)ᵀ * X.J.map t * gs) =
          (X.J.map t)⁻¹ * (((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * (g'.val)ᵀ) * X.J.map t * gs by
            simp only [Matrix.mul_assoc],
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one,
        Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
    rw [e, hUt]
  have hgA : At (evFin F v) (mat g - 1) := hg
  have hLA : At (evFin F v) (mat L - 1) := GlobalTheory.SplitUnitLift.liftU_mem_UAt h t X 1 herm hJ g'
  have hLt : (mat L).map (piW t) = g'.val := GlobalTheory.SplitUnitLift.liftU_piW h t X.J 1 herm hJ g'
  have hLs : (mat L).map (piW (t.comp σ)) = (X.J.map t)⁻¹ * ((g'⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * X.J.map t :=
    GlobalTheory.SplitUnitLift.liftU_piW_comp h t X.J 1 herm hJ g'
  apply Subtype.ext
  apply Units.ext
  show mat g = mat L
  ext i j
  rw [← sub_eq_zero]
  have hz : mat g i j - mat L i j = (mat g - 1) i j - (mat L - 1) i j := by
    simp only [Matrix.sub_apply]; ring
  refine GlobalTheory.VacIso.eq_zero_of_at_split h t ?_ ?_ ?_
  · intro u hu
    have e1 := congrFun (congrFun (hgA u hu) i) j
    have e2 := congrFun (congrFun (hLA u hu) i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply] at e1 e2
    rw [hz, smul_sub, e1, e2, sub_zero]
  · have e1 := congrFun (congrFun hLt i) j
    have e2 := congrFun (congrFun hv i) j
    simp only [Matrix.map_apply] at e1 e2
    rw [map_sub, e1, ← e2, sub_self]
  · have e1 := congrFun (congrFun hLs i) j
    have e2 := congrFun (congrFun hσ i) j
    simp only [hgs, Matrix.map_apply] at e1 e2
    rw [map_sub, e1, e2, sub_self]

end GlobalTheory.SchurCharV


open GlobalTheory.SchurCharV in
theorem GlobalTheory.SchurCharV.exists_char_of_schur : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ g ∈ UAt σ G.V (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (((mat g).map (piW t))⁻¹ * Y)) →
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t ι hι H
  have hcm : IsCMExt F E σ := hT.base.cm
  have herm : ∀ i j, σ (G.V.J j i) = algebraMap F E 1 * G.V.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV.herm i j
  have hJ : IsUnit (G.V.J.map t).det := by
    have w := Classical.arbitrary (InfinitePlace F)
    exact GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V.J t (B.emb w).1 1 one_ne_zero (G.V.θ w)
      (by rw [one_smul]; exact hT.geo.hV.cartan w)
  set L := GlobalTheory.SplitUnitLift.liftU hcm t G.V.J 1 herm hJ with hLdef
  have hLmem : ∀ x, L x ∈ UAt σ G.V (evFin F v) := fun x => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V 1 herm hJ x
  have hLt : ∀ x, (mat (L x)).map (piW t) = x.val := fun x => GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V.J 1 herm hJ x
  have hEx := (GlobalTheory.T.theta_action_exists hP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1
  have h1mem : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.W.J) - 1) = 0
    rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]
  have hpres : ∀ p : UA σ G.V.J × UA σ G.W.J, ∀ Φ ∈ schA F (Fin a × Fin (a + a')),
      om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ
  have hvac := hT.geo.hM.vac v
  set φv := G.M.vac v
  have hφv : φv ∈ SB (Fin a × Fin (a + a') → Fv F v) := hvac.1
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hιv : ι φv ≠ 0 := fun h0 => hvac.2.1 (hbij.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  choose c hc using fun x : GL (Fin a) (Fv F v) => H (L x) (hLmem x)
  have hrel : ∀ x, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (L x, 1)) φ φ₁ → ∀ Y, ι φ₁ Y = c x * ι φ ((x⁻¹ : GL (Fin a) (Fv F v)).val * Y) := by
    intro x φ hφ φ₁ hφ₁ hA Y
    rw [hc x φ hφ φ₁ hφ₁ hA Y, hLt x, Matrix.coe_units_inv]
  have hmul : ∀ x y, c (x * y) = c x * c y := by
    intro x y
    obtain ⟨φ₂, ⟨hφ₂, hA₂⟩, -⟩ := hEx (L y) (hLmem y) 1 h1mem φv hφv
    obtain ⟨φ₃, ⟨hφ₃, hA₃⟩, -⟩ := hEx (L x) (hLmem x) 1 h1mem φ₂ hφ₂
    have hA : Acts (evFin F v) (om (L (x * y), 1)) φv φ₃ := by
      have e : ((L (x * y), 1) : UA σ G.V.J × UA σ G.W.J) = (L x, 1) * (L y, 1) := by
        rw [Prod.mk_mul_mk, map_mul, one_mul]
      rw [e, map_mul]
      exact GlobalTheory.InertAvgDual.acts_comp v _ _ (hpres _) hA₂ hA₃
    have e1 := hrel (x * y) φv hφv φ₃ hφ₃ hA ((x * y).val * Y₀)
    have e2 := hrel x φ₂ hφ₂ φ₃ hφ₃ hA₃ ((x * y).val * Y₀)
    have e3 := hrel y φv hφv φ₂ hφ₂ hA₂ (y.val * Y₀)
    have k1 : ((x * y)⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have k2 : (x⁻¹ : GL (Fin a) (Fv F v)).val * ((x * y).val * Y₀) = y.val * Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel_left]
    have k3 : (y⁻¹ : GL (Fin a) (Fv F v)).val * (y.val * Y₀) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    rw [e2, e3] at e1
    exact mul_right_cancel₀ hY₀ (e1.symm.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have hA : Acts (evFin F v) (om (L 1, 1)) φv φv := by
      rw [map_one, show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
      exact GlobalTheory.InertAvgDual.acts_one v φv
    have e := hrel 1 φv hφv φv hφv hA Y₀
    rw [inv_one, Units.val_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e.symm
  let cH : GL (Fin a) (Fv F v) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) cH.toHomUnits
  have hcχ : ∀ x, c x = (χ (Matrix.GeneralLinearGroup.det x) : ℂ) := fun x => by rw [← hχ x]; rfl
  let A : (Fv F v)ˣ →* ℂˣ :=
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (((a + a' : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  refine ⟨(χ * A)⁻¹, ?_⟩
  intro g hg
  set g' := Matrix.GeneralLinearGroup.map (piW t) g.1 with hg'
  refine ⟨g', rfl, ?_⟩
  intro φ hφ φ₁ hφ₁ hA
  have hgL : g = L g' := eq_liftU_of_UAt hcm t G.V herm hJ g hg
  rw [hgL] at hA
  funext Y
  rw [hrel g' φ hφ φ₁ hφ₁ hA Y, hcχ g']
  have hpow : ∀ d : (Fv F v)ˣ, GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) *
      GlobalTheory.SplitFlip.apow d (-((a + a' : ℕ) : ℂ) / 2) = 1 := fun d => by
    rw [← GlobalTheory.SplitFlip.apow_add, show ((a + a' : ℕ) : ℂ) / 2 + -((a + a' : ℕ) : ℂ) / 2 = 0 by ring,
      GlobalTheory.SplitFlip.apow_zero]
  simp only [GlobalTheory.SplitFlip.omA, MonoidHom.inv_apply, inv_inv, MonoidHom.mul_apply, Units.val_mul, map_one,
    MonoidHom.one_apply, Units.val_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]
  have hAv : ∀ d, ((A d : ℂˣ) : ℂ) = GlobalTheory.SplitFlip.apow d (((a + a' : ℕ) : ℂ) / 2) := fun d => rfl
  rw [hAv]
  linear_combination (-(χ (GlobalTheory.SplitFlip.gdet g') : ℂ) * ι φ ((g'⁻¹ : GL (Fin a) (Fv F v)).val * Y)) * hpow (GlobalTheory.SplitFlip.gdet g')
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthOverDvrEqOverClosedField
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DepthDescent

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem nuLocOf_eq_nuLocX_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e ho y Ch X cx n B k
  have hp0 : 0 ≤ vV T.V (p : T.Fr) := by
    have := GlobalTheory.vV_algebraMap_nonneg_dvr T (p : T.V)
    rwa [map_natCast] at this
  have he : vV T.V (p : T.Fr) = (((vV T.V (p : T.Fr)).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hp0).symm
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hh : MvPowerSeries.constantCoeff Ch.ch.h = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ Ch.ch.gauge.ax0 0 fun _ => rfl
  have hu : (fun (ℓ : LtN Dw n) => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) =
      fun ℓ j => X.ιF (Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j) := by
    funext ℓ j
    simp only [lieVec, jX, RingHom.comp_apply]
    rw [Ch.gen.1.2.2.2.2.2.2]
  have himg : ∀ f : PS T.Fr n (chD Ch.ch), nabX Ch X cx B k (MvPowerSeries.map X.ιF f) =
      X.ιF (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (polyT B cx)) := by
    intro f
    unfold nabX
    rw [hu]
    exact GlobalTheory.ThetaLeast.nabValN_algebraMap T.Fr X.C _ _ Ch.ch.B Ch.ch.h hh H.w0 k n f _ _ _ _
  have hB : ∀ g : PS X.C n (chD Ch.ch), nabX Ch X cx B k g =
      nabValN (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B) X.C (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k g
        (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩)
        (MvPolynomial.map X.ιF (polyT B cx)) := by
    intro g
    have h1 : (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B).FK X.C = Ch.ch.B.FK X.C := by
      funext i
      ext μ
      simp [FB.FK, FGLaw.mapF, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapLaw, GlobalTheory.FBMap.mapPt, RingHom.algebraMap_toAlgebra]
    have h2 : ∀ b, (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B).actK X.C b = Ch.ch.B.actK X.C b := by
      intro b
      funext i
      ext μ
      simp [FB.actK, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapAct, GlobalTheory.FBMap.mapPt, RingHom.algebraMap_toAlgebra]
    unfold nabX nabValN FB.hL
    rw [h1, h2]
  apply le_antisymm
  · unfold nuLocX_vp
    refine le_iInf fun g => ?_
    obtain ⟨S, hS⟩ := GlobalTheory.nabValN_eq_sum_coeff X.C _ _ (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B)
      (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k n (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx))
    have hμ : ∀ μ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) ≤
        toE (vX_vp X (nabX Ch X cx B k (MvPowerSeries.monomial μ (1 : X.C)))) := by
      intro μ
      have hmon : (MvPowerSeries.monomial μ (1 : X.C) : PS X.C n (chD Ch.ch))
          = MvPowerSeries.map X.ιF (MvPowerSeries.monomial μ (1 : T.Fr) : PS T.Fr n (chD Ch.ch)) := by
        rw [MvPowerSeries.map_monomial, map_one X.ιF]
      rw [hmon, himg, toE_vX_vp_ιF X he]
      unfold nuLocOf
      refine iInf₂_le_of_le (MvPowerSeries.monomial μ (1 : T.Fr)) (fun ρ => ?_) le_rfl
      classical
      rw [MvPowerSeries.coeff_monomial]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    rw [hB, hS g.1]
    simp only [← hB]
    generalize nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = ν at hμ ⊢
    induction ν using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe w =>
      refine WithBot.coe_le_coe.2 ?_
      refine (vX_vp X).map_le_sum fun μ _ => ?_
      rw [(vX_vp X).map_mul]
      exact le_trans (WithBot.coe_le_coe.1 (hμ μ)) (le_add_of_nonneg_left (g.2 μ))
  · unfold nuLocOf nuLocX_vp
    refine le_iInf₂ fun f hf => ?_
    refine iInf_le_of_le ⟨MvPowerSeries.map X.ιF f, fun α => ?_⟩ (le_of_eq ?_)
    · obtain ⟨t, ht⟩ := hf α
      rw [MvPowerSeries.coeff_map, ← ht]
      exact isIntV_jX X t
    · rw [himg, toE_vX_vp_ιF X he]

end GlobalTheory.DepthDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInf
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.PureStabOne

theorem pure_stab_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ' : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ' w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ≠ v → φ' w = φ w) ∧ Acts (evFin F v) (om' (g, h)) (φ v) (φ' v) ∧ om' (g, h) (pure f φ) = pure f φ' := by
  classical
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v g hg h hh f φ hSB hvac
  have hpair := GlobalTheory.ThK.Inhab.pairV' hT
  obtain ⟨φ₁, ⟨hφ₁SB, hAct⟩, -⟩ :=
    ((GlobalTheory.T.theta_action_exists hP) F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hpair v).1 g hg h hh (φ v) (hSB v)
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hvac, hT.geo.hM'.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  refine ⟨Function.update φ v φ₁, fun w => ?_, fun w hw => Function.update_of_ne hw _ _, ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ₁SB
    · rw [Function.update_of_ne hw]; exact hSB w
  · rw [Function.update_self]; exact hAct
  · have e1 : pure f φ = tens (evFin F v) (φ v) r := by rw [hrt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) r := ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    rw [e1, hAct r hRest, hrt]

end GlobalTheory.PureStabOne

end
end

