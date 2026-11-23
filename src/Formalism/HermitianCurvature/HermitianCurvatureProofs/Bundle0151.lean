module

public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.StatementPB
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormModel
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def FormModel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (a : ℝ) (mm : ℕ)
    (ε' : ℝ) (Sg : Set (B.Mat P0.k (P0.r - j))),
    0 < ε' → P5.Auser P0 w.length + 1 ≤ a → P5.mmUser P0 w.length ≤ mm →
    5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm →
    (∀ γ ∈ Sg, ε' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' γ) →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
      (Mo : U.CCModel P0.k (P0.r - j) (Wd.Ix (Fin w.length) → (Wq →L[ℂ] Wp)) a mm Sg V),
      ∃ (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Cp : ℝ), 0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
        ∀ (u u' : V) (x x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε'' : ℝ), 0 < ε'' →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x e)) →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x' e)) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u γ e = x e γ) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u' γ e = x' e γ) →
          Bf u u' = D.formLev T sg j w x x'

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDerivativeHolds
section
namespace Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

open Formalism.FourierDecayAlt.PB Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem localCores : Formalism.FourierDecayAlt.PB.LocalCores :=
  ⟨Formalism.FourierDecayAlt.Final.jx_pSDAgree,
   Formalism.FourierDecayAlt.Final.jx_schurProduct,
   Formalism.FourierDecayAlt.Final.jx_productDomination,
   Formalism.FourierDecayAlt.Final.jx_diagScale,
   Formalism.FourierDecayAlt.Final.jx_diagPhase,
   Formalism.FourierDecayAlt.Final.jx_blockDiagPSD,
   Formalism.FourierDecayAlt.Final.jx_productLemma,
   Formalism.FourierDecayAlt.Final.jx_scaleOk,
   Formalism.FourierDecayAlt.Final.jx_phaseOk,
   Formalism.FourierDecayAlt.Final.jx_outsideSysOk,
   Formalism.FourierDecayAlt.Final.jx_outsideDomination,
   Formalism.FourierDecayAlt.Final.jx_localPullback,
   Formalism.FourierDecayAlt.Final.jx_localUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_topPullback,
   Formalism.FourierDecayAlt.Final.jx_topUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_globalOfLocal,
   Formalism.FourierDecayAlt.Final.jx_uniformMajorantOn,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromSystems,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromFamilies,
   Formalism.FourierDecayAlt.Final.jx_kernelOfLocal,
   Formalism.FourierDecayAlt.Final.jx_localKernelPSD,
   Formalism.FourierDecayAlt.Final.tc_domMinOfText,
   Formalism.FourierDecayAlt.Final.tc_domAfterOfLocal,
   Formalism.FourierDecayAlt.Final.gram_determinant_dual_bound_a,
   Formalism.FourierDecayAlt.Final.parahoric_gram_matrix,
   Formalism.FourierDecayAlt.Final.zero_level_ones_vector,
   Formalism.FourierDecayAlt.Final.singleBlockParseval_true,
   Formalism.FourierDecayAlt.Final.theta_equality_first,
   Formalism.FourierDecayAlt.Final.singleBlockThetaProps_true,
   Formalism.FourierDecayAlt.Final.ns_support,
   Formalism.FourierDecayAlt.Final.ns_block_diagonal,
   Formalism.FourierDecayAlt.Final.latticeAverage_of_gram⟩

theorem globalCores : Formalism.FourierDecayAlt.PB.GlobalCores :=
  ⟨Formalism.FourierDecayAlt.Final.tc_theoremAAfter,
   Formalism.FourierDecayAlt.Final.tc_recursionWithDens,
   Formalism.FourierDecayAlt.Final.tc_domScaleTop,
   Formalism.FourierDecayAlt.Final.tc_sumBoundMax,
   Formalism.FourierDecayAlt.Final.tc_recHypScaleTop,
   Formalism.FourierDecayAlt.Final.tc_densSum,
   Formalism.FourierDecayAlt.Final.tc_densLeTwo,
   Formalism.FourierDecayAlt.Final.tc_densSize,
   Formalism.FourierDecayAlt.Final.tc_densChain,
   Formalism.FourierDecayAlt.Final.poisson_summation_text,
   Formalism.FourierDecayAlt.Final.jx_poissonJoint,
   Formalism.FourierDecayAlt.Final.jx_poissonStepJoint,
   Formalism.SA.P.smoothedSumBound,
   Formalism.FourierDecayAlt.Final.lattices_general_position_bound,
   Formalism.FourierDecayAlt.Final.ideals_match,
   Formalism.FourierDecayAlt.Final.ideal_norm_formula,
   Formalism.FourierDecayAlt.Final.field_extension_degree_facts,
   Formalism.FourierDecayAlt.Final.jx_frameProducts,
   Formalism.FourierDecayAlt.Final.jx_xIsLamOne,
   Formalism.FourierDecayAlt.Final.jx_latticeSumsJoint,
   Formalism.FourierDecayAlt.Final.jx_instSizes,
   Formalism.FourierDecayAlt.Final.jx_instLatticeSums,
   Formalism.FourierDecayAlt.Final.sz_sizesMain,
   Formalism.FourierDecayAlt.Final.jx_sizesToRecursion,
   Formalism.FourierDecayAlt.Final.jx_globPositive,
   Formalism.FourierDecayAlt.Final.counting_theorem,
   Formalism.FourierDecayAlt.Final.jx_formGivesMain⟩

end Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntCut
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def SliceIntCut : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε : ℝ) (i : ℕ) (hi : i ≤ P0.r),
    1 ≤ i → 2 ≤ P0.k → B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) →
    C6.IsCut0 χ → 0 < ε → ∀ (p : C.LPt) (hp : D.IsLocPt p i), ∀ (e : Wd.Ix (Fin w.length)),
    ∀ γ ∈ B.GV P0.k (P0.r - D.ptSize p),
    Integrable (fun ξ : U.Xi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.castV (by have := hp.2; omega) T.base.z) (D.castV (by have := hp.2; omega) T.base.z') ξ •
          D.castF (by have := hp.2; omega) (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e)
            (U.gaXi P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def kapB (n : ℕ) : ℝ := Real.pi ^ ((n + 1) * (n + 4) / 2)

theorem ptSize_two (h : C.LPt) (n : ℕ) (t c : ℂ) :
    D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := by
  simp [D.ptSize, List.map_append, List.sum_append]

def SliceOmBlock : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h p : C.LPt) (n : ℕ) (t c : ℂ)
    (hp : p = h ++ [(n + 1, t), (1, c)]) (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)),
    D.IsLocPt p (D.ptSize p) →
    Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) →
    D.sliceAt k r z z' F p γ =
      ((kapB n : ℝ) : ℂ) •
        G.OmBlock U.betaU (n + 1) (fun Z => U.PhiFun k (r - D.ptSize p) (D.ptPerm h) (D.ptDiag h)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z')
          (D.castF (by subst hp; rw [ptSize_two] at hle ⊢; omega) F) Z γ) t c

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herKc_sliceIn : SliceIn (S := S) P z z' π π' L st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l x hx
  exact inK_act_span (bTl L l w) (fun a b Φ hΦ => Submodule.subset_span (HerGenC.slice l w a b Φ hw hΦ)) x hx

theorem herKc_waveK : WaveK (S := S) P z z' π π' st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l s Wv Wv' hW hW' x hx
  exact inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveC l w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_waveZ (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')) (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) (x : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) x) :
    InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) (act (Vw (mkP Wv Wv') s w) x) :=
  inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveZ w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

end Classes

def HerCptTopAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    herKc S P z z' π π' L st l0 D (Fin.last P.r) ≤ cptSub P.k P.r z z' π π'

def StepFormCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0 ∧
      FormInt S P z z' π π' μ L st l0 (herKc S P z z' π π' L st l0 D)

theorem thmPActualCpt_of_herClassesCpt (hHer : HerClassesCpt) (hWC : WaveCommQQAll) : ThmPActualCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, hAdj, hTD, hTT, hSl, hSD, hWK, hFS, hCor, hJ⟩ :=
    hHer Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  refine ⟨K, ?_, hSl, hCor, hJ⟩
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hST := stepTwistFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.plane_wave_vector_identity
    (waveSiteAll Wp Wq P z z' π π' X L) (hWC Wp Wq P z z' π π' X μ L st l0 hD) hWK
  exact thmPFromStepsAll Wp Wq S P z z' π π' μ L st K l0 hTI hTD hTT hSl hSD hST hFS

theorem herClassesCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : HerClassesCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' _ _
  obtain ⟨hSD, hFI⟩ := hSF Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  set K := herKc S P z z' π π' L st l0 D with hKdef
  haveI : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hAdj : AdjTop (S := S) P z z' π π' μ L st K l0 :=
    adjTop_cpt P z z' π π' X μ L st K l0 hD (hT Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ')
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD
    Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hXK := xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 K hD hl1 hl2 hXK
  have hCor := integral_formula_of_steps Wp Wq S P z z' π π' μ L st l0 K hTI hTD herKc_sliceIn hSD
    (topDensMeasAll Wp Wq S P z z' π π' μ L st K)
  have hTT := topTwistDensOfZeta Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt Wp Wq S P z z' π π' X μ L st l0 K hD
  have hFS := formSesqOfInt Wp Wq S P z z' π π' μ L st l0 _ hFI
  refine ⟨K, hAdj, hTD, ?_, herKc_sliceIn, hSD, herKc_waveK, hFS, hCor, ?_⟩
  · intro w hw s Wv Wv' hW hW' x y hx hy c hc
    exact ⟨herKc_waveZ w hw s Wv Wv' hW hW' x hx, hTT w hw s Wv Wv' hW hW' x y hx hy c hc⟩
  · intro F ε hε hF hC hG
    obtain ⟨Φ, hΦ⟩ := radJFExists Wp Wq P z z' π π' D F hD.1 hz hz' hπ hπ' ⟨hF, ε, hε, hG⟩
    exact ⟨Φ, herKc_jf F ⟨⟨hF, ε, hε, hG⟩, hC⟩ Φ hΦ, hΦ⟩

theorem thmPActualCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : ThmPActualCpt :=
  thmPActualCpt_of_herClassesCpt (herClassesCpt_of_parts hT hSF) waveCommQQAll

end Formalism.FourierDecayAlt.P5.HerC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemTsupportPsiL
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section LogBump

def bumpR : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

def psiL (n : ℕ) (c : ℂ) : ℝ := if c = 0 then 0 else bumpR (Real.log ‖c‖ / ((n : ℝ) + 1))

theorem psiL_le_one (n : ℕ) (c : ℂ) : |psiL n c| ≤ 1 := by
  unfold psiL
  split_ifs
  · simp
  · rw [abs_of_nonneg bumpR.nonneg]
    exact bumpR.le_one

theorem psiL_eq_near (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    psiL n =ᶠ[𝓝 c] fun w => bumpR (Real.log ‖w‖ / ((n : ℝ) + 1)) := by
  filter_upwards [isOpen_ne.mem_nhds hc] with w hw
  simp [psiL, hw]

theorem psiL_zero_of (n : ℕ) (w : ℂ) (hw : 2 * ((n : ℝ) + 1) ≤ |Real.log ‖w‖|) : psiL n w = 0 := by
  unfold psiL
  split_ifs with h
  · rfl
  · apply bumpR.zero_of_le_dist
    have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, le_div_iff₀ hpos]
    exact hw

theorem psiL_one_near (n : ℕ) (c : ℂ) (hc : c ≠ 0) (h : |Real.log ‖c‖| < (n : ℝ) + 1) :
    psiL n =ᶠ[𝓝 c] fun _ => 1 := by
  have hcont : ContinuousAt (fun w : ℂ => |Real.log ‖w‖|) c :=
    ((Real.continuousAt_log (norm_ne_zero_iff.2 hc)).comp continuous_norm.continuousAt).abs
  have h1 : ∀ᶠ w in 𝓝 c, |Real.log ‖w‖| < (n:ℝ) + 1 := hcont.eventually_lt continuousAt_const h
  filter_upwards [isOpen_ne.mem_nhds hc, h1] with w hw hw1
  simp only [psiL, if_neg hw]
  apply bumpR.one_of_mem_closedBall
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  show |Real.log ‖w‖| ≤ 1 * ((n:ℝ) + 1)
  linarith

theorem psiL_zero_near0 (n : ℕ) : psiL n =ᶠ[𝓝 0] fun _ => 0 := by
  have hε : (0:ℝ) < Real.exp (-(2 * ((n:ℝ) + 1))) := Real.exp_pos _
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hε] with w hw
  by_cases h0 : w = 0
  · simp [psiL, h0]
  · apply psiL_zero_of
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hlog : Real.log ‖w‖ < -(2 * ((n:ℝ) + 1)) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.2 h0)]
      exact hw
    have h2 : (0:ℝ) < 2 * ((n:ℝ) + 1) := by positivity
    rw [abs_of_neg (by linarith)]
    linarith

theorem psiL_contDiffAt (n : ℕ) (c : ℂ) : ContDiffAt ℝ ∞ (psiL n) c := by
  by_cases hc : c = 0
  · subst hc
    exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq (psiL_zero_near0 n)
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (psiL_eq_near n c hc)
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) c := contDiffAt_norm ℝ hc
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) c :=
      (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hc)).comp c h1
    have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1)) c := h2.div_const _
    exact bumpR.contDiff.contDiffAt.comp c h3

theorem psiL_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiL n) := contDiff_iff_contDiffAt.2 (psiL_contDiffAt n)

theorem tsupport_psiL (n : ℕ) : tsupport (psiL n) ⊆
    {c : ℂ | Real.exp (-(2 * ((n : ℝ) + 1))) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp (2 * ((n : ℝ) + 1))} := by
  refine closure_minimal (fun c hc => ?_)
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
  have hc' : psiL n c ≠ 0 := hc
  have h0 : c ≠ 0 := by
    rintro rfl
    exact hc' (by simp [psiL])
  have hlog : |Real.log ‖c‖| < 2 * ((n:ℝ) + 1) := by
    by_contra hle
    push_neg at hle
    exact hc' (psiL_zero_of n c hle)
  have hpos := norm_pos_iff.2 h0
  rw [abs_lt] at hlog
  constructor
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith [hlog.1])
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith [hlog.2])

theorem psiL_hasCompactSupport (n : ℕ) : HasCompactSupport (psiL n) := by
  refine (isCompact_closedBall (0:ℂ) (Real.exp (2 * ((n:ℝ) + 1)))).of_isClosed_subset (isClosed_tsupport _) ?_
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (tsupport_psiL n hc).2

theorem zero_notMem_tsupport_psiL (n : ℕ) : (0 : ℂ) ∉ tsupport (psiL n) := by
  intro h
  have h1 := (tsupport_psiL n h).1
  rw [norm_zero] at h1
  exact absurd h1 (not_le.2 (Real.exp_pos _))

theorem exists_deriv_bump_bound : ∃ C : ℝ, ∀ t, ‖deriv bumpR t‖ ≤ C := by
  have hc : Continuous (deriv bumpR) := (bumpR.contDiff (n := 1)).continuous_deriv le_rfl
  exact hc.bounded_above_of_compact_support bumpR.hasCompactSupport.deriv

theorem norm_mul_fderiv_psiL_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    ‖c‖ * ‖fderiv ℝ (psiL n) c‖ ≤ C := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hnd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) c := (contDiffAt_norm ℝ hc (n := 1)).differentiableAt one_ne_zero
  have hN : ‖fderiv ℝ (fun w : ℂ => ‖w‖) c‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := c) lipschitzWith_one_norm
  have hl : HasFDerivAt (fun w : ℂ => Real.log ‖w‖) ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c) c :=
    (Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt c hnd.hasFDerivAt
  have hφ : HasFDerivAt (fun w : ℂ => Real.log ‖w‖ / ((n:ℝ) + 1))
      ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) c := by
    have h2 := hl.mul_const (((n:ℝ) + 1)⁻¹)
    simpa only [div_eq_mul_inv] using h2
  have hb : HasDerivAt (⇑bumpR) (deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1))) (Real.log ‖c‖ / ((n:ℝ) + 1)) :=
    ((bumpR.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hcomp := hb.comp_hasFDerivAt c hφ
  have hf : fderiv ℝ (psiL n) c = deriv bumpR (Real.log ‖c‖ / ((n:ℝ) + 1)) •
      ((((n:ℝ) + 1)⁻¹) • ((‖c‖)⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) c)) :=
    (psiL_eq_near n c hc).fderiv_eq.trans hcomp.fderiv
  have e1 : ‖(((n:ℝ) + 1)⁻¹)‖ = ((n:ℝ) + 1)⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1)]
  have e2 : ‖(‖c‖)⁻¹‖ = (‖c‖)⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  rw [hf, norm_smul, norm_smul, norm_smul, e1, e2]
  have hinv : ((n:ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  have key : ∀ (t a b N : ℝ), 0 < t → a ≤ C → 0 ≤ a → 0 ≤ b → b ≤ 1 → 0 ≤ N → N ≤ 1 →
      t * (a * (b * (t⁻¹ * N))) ≤ C := by
    intro t a b N ht ha ha0 hb0 hb1 hN0 hN1
    rw [show t * (a * (b * (t⁻¹ * N))) = a * (b * N) * (t * t⁻¹) by ring, mul_inv_cancel₀ ht.ne', mul_one]
    calc a * (b * N) ≤ C * (1 * 1) :=
          mul_le_mul ha (mul_le_mul hb1 hN1 hN0 zero_le_one) (mul_nonneg hb0 hN0) (le_trans ha0 ha)
      _ = C := by ring
  exact key _ _ _ _ hpos (hC _) (norm_nonneg _) (inv_nonneg.2 hn1.le) hinv (norm_nonneg _) hN

end LogBump

end Formalism.FourierDecayAlt.P5.HerB
end
end

