module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0256
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCore
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0254
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0255
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0252
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0251
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNConjTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0245
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0248
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnlyOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0247

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_RDWave
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_wave_identity : RDWave := by
  intro k r Wp Wq _ _ _ _ _ _ D hr ε s G
  have h1 : 1 < r + 2 := by omega
  refine ⟨fun hG => Formalism.FourierDecayAlt.P.PBFV.good_fsv_dmin D ε s h1 G hG, fun y hy => ?_⟩
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  simp only [resG]
  rw [show wvG D.z D.z' s G = fun g => fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • G g from rfl,
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv G]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord D.z_mem D.z'_mem hr y.1 hy.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGAsm
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sliceFamGood_of (hGf : GfStep) (hRP : RadProper) (hPS : ParamSmooth) (hPt : PtSmooth) (hGV : PtGV)
    (hE : CkExt) : CutSH.SliceFamGood := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j hj _ _ F hF
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  obtain ⟨⟨hcc, ε, hε, hFG⟩, hcs⟩ := hF
  have hFs : B.CkOn (⊤ : ℕ∞) (B.GV P.k (P.r - j)) F :=
    Formalism.FourierDecayAlt.P.PBE.ckOn_top_of_nat fun m => (hcc 0 m).choose_spec.1
  obtain ⟨Ft, hFt, -, hFtF⟩ := hE P.k (P.r - j) _ F hFs hcs
  obtain ⟨R, hR⟩ := (hcs.isCompact.image_of_continuousOn
    (Formalism.FourierDecayAlt.P.B6.gN_continuous (k := P.k) (r := P.r - j)).continuousOn).bddAbove
  have hRF : ∀ g, F g ≠ 0 → B.gN g ≤ R := fun g hne => hR ⟨g, subset_tsupport _ hne, rfl⟩
  have hsl : ∀ (t : ℂ) (γ : B.Mat P.k (P.r - (j + 1))), γ ∈ B.GV P.k (P.r - (j + 1)) → sliceFam T j hj F t γ =
      ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) * star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
          F (pt e t γ xx) ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))) := by
    intro t γ hγ
    unfold sliceFam
    rw [Set.indicator_of_mem hγ]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro t₀ ht₀ γ₀ _
    have ht₀p : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀
    set δ : ℝ := ‖t₀‖ / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    obtain ⟨Kx, C, hKx, -, hKC⟩ := hRP P.k (P.r - (j + 1)) (P.r - j) e δ R hδ0
    obtain ⟨R1, hR1⟩ :=
      hKx.isBounded.subset_closedBall (0 : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)))
    have : HasContDiffBump (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) := inferInstance
    set χ : ContDiffBump (0 : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) :=
      ⟨max R1 0 + 1, max R1 0 + 2, by positivity, by linarith⟩ with hχ
    set s : Set (ℂ × B.Mat P.k (P.r - (j + 1))) := {p | δ < ‖p.1‖} with hs
    have hso : IsOpen s := isOpen_lt continuous_const (continuous_norm.comp continuous_fst)
    have hs0 : ∀ p ∈ s, p.1 ≠ 0 := fun p hp => norm_pos_iff.1 (hδ0.trans hp)
    set hI : ℂ × B.Mat P.k (P.r - (j + 1)) → U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)) →
        (Wq →L[ℂ] Wp) :=
      fun p xx => χ xx • ((psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
        star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) • Ft (pt e p.1 p.2 xx)) with hIdef
    refine ⟨s, fun p => ((‖p.1‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
      ∫ xx, hI p xx ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))), hso, ?_, ?_, ?_⟩
    · show δ < ‖t₀‖
      rw [hδ]; linarith
    ·
      have : BorelSpace (U.RC P.k 1 (P.r - (j + 1))) := Prod.borelSpace
      have : BorelSpace (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) := Prod.borelSpace
      have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := P.k) 1 (P.r - (j + 1))
      have := Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas.fmc_RC P.k 1 (P.r - (j + 1))
      have hsc : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) =>
          ((‖p.1‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ)) s := by
        intro p hp
        have hn : ContDiffAt ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => ‖p.1‖) p :=
          (contDiffAt_norm ℝ (hs0 p hp)).comp p contDiffAt_fst
        exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hn.pow _)).contDiffWithinAt
      have hps := (hPt P.k (P.r - (j + 1)) (P.r - j) e).2
      have hpt := (hPt P.k (P.r - (j + 1)) (P.r - j) e).1
      have hjoint : ContDiffOn ℝ ∞
          (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) × (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) =>
            hI q.1 q.2) (s ×ˢ Set.univ) := by
        have h1 : ContDiff ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) => χ q.2) :=
          χ.contDiff.comp contDiff_snd
        have h2 : ContDiff ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) =>
            psi P.k (P.r - j) (T.bs j).z cStd (rn1 e q.2.1) *
              star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e q.2.2))) := by
          refine ((hps (T.bs j).z).comp (contDiff_fst.comp contDiff_snd)).mul ?_
          exact Complex.conjCLE.contDiff.comp ((hps (T.bs j).z').comp (contDiff_snd.comp contDiff_snd))
        have h3 : ContDiffOn ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) => Ft (pt e q.1.1 q.1.2 q.2))
            (s ×ˢ Set.univ) :=
          hFt.comp_contDiffOn (hpt.mono (Set.prod_mono (fun p hp => hs0 p hp) le_rfl))
        exact h1.contDiffOn.smul (h2.contDiffOn.smul h3)
      have hvan : ∀ p ∈ s, ∀ xx, xx ∉ tsupport χ → hI p xx = 0 := by
        intro p _ xx hxx
        simp only [hIdef, image_eq_zero_of_notMem_tsupport hxx, zero_smul]
      have hint := hPS _ _ _ ((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))) hI s
        (tsupport χ) hso χ.hasCompactSupport hvan hjoint
      exact hsc.smul hint
    ·
      rintro ⟨t, γ⟩ hp hγ
      have ht : t ≠ 0 := hs0 _ hp
      have hδt : δ ≤ ‖t‖ := le_of_lt hp
      show sliceFam T j hj F t γ = _
      rw [hsl t γ hγ]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
      have hpG := hGV P.k (P.r - (j + 1)) (P.r - j) e t ht γ hγ xx
      have hFt' : Ft (pt e t γ xx) = F (pt e t γ xx) := hFtF _ hpG
      show _ = hI (t, γ) xx
      simp only [hIdef]
      rw [hFt']
      by_cases hF0 : F (pt e t γ xx) = 0
      · simp only [hF0, smul_zero]
      · have hxK : xx ∈ Kx := (hKC t γ xx hδt (hRF _ hF0)).1
        have h1 : χ xx = 1 := by
          apply χ.one_of_mem_closedBall
          have := hR1 hxK
          rw [Metric.mem_closedBall] at this ⊢
          show dist xx 0 ≤ max R1 0 + 1
          linarith [le_max_left R1 0]
        rw [h1, one_smul]
  ·
    intro K hK hK0
    by_cases hne : K.Nonempty
    · obtain ⟨t1, ht1K, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
      have hδ0 : 0 < ‖t1‖ := norm_pos_iff.2 (hK0 t1 ht1K)
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
      have hM' : ∀ t ∈ K, ‖t‖ ≤ M := fun t ht => by simpa using hM t ht
      have hMp : 0 < M := hδ0.trans_le (hM' t1 ht1K)
      obtain ⟨Kx, C, -, hC, hKC⟩ := hRP P.k (P.r - (j + 1)) (P.r - j) e ‖t1‖ R hδ0
      refine ⟨C, hC, ε / M ^ 2, by positivity, ?_⟩
      intro t htK γ hne'
      have ht : t ≠ 0 := hK0 t htK
      have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
        by_contra hγ
        apply hne'
        unfold sliceFam
        rw [Set.indicator_of_notMem hγ]
      rw [hsl t γ hγ] at hne'
      obtain ⟨xx, hxx⟩ : ∃ xx, F (pt e t γ xx) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne'
        simp only [hall, smul_zero, integral_zero]
      have hδt : ‖t1‖ ≤ ‖t‖ := hmin htK
      refine ⟨(hKC t γ xx hδt (hRF _ hxx)).2, fun _ => ?_⟩
      have hpG := hGV P.k (P.r - (j + 1)) (P.r - j) e t ht γ hγ xx
      have h1 : ε ≤ Gf P.k (P.r - j) (T.bs j).z (T.bs j).z' (pt e t γ xx) := hFG _ hpG hxx
      have hz : (T.bs j).z = D.castV e (D.castV (Nat.add_comm 1 (P.r - (j + 1)))
          (liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z)) := by
        rw [levTower_bs_z_eq_castV_liftVec T j hj, asm_castV_castV]
      have hz' : (T.bs j).z' = D.castV e (D.castV (Nat.add_comm 1 (P.r - (j + 1)))
          (liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z')) := by
        rw [levTower_bs_z'_eq_castV_liftVec T j hj, asm_castV_castV]
      rw [hz, hz', hGf P.k (P.r - (j + 1)) (P.r - j) e _ _ (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem t ht γ xx]
        at h1
      have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
      have htM : ‖t‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM' t htK) 2
      have hG0 : 0 < Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ := by
        by_contra hle
        push Not at hle
        have : ‖t‖ ^ 2 * Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · exact ⟨∅, isCompact_empty, 1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne⟩

end Formalism.FourierDecayAlt.P.CutSH.SFG

namespace Formalism.FourierDecayAlt.P.CutSH

theorem cutSH_sliceFamGood_of (hGf : SFG.GfStep) (hRP : SFG.RadProper) (hPS : SFG.ParamSmooth)
    (hPt : SFG.PtSmooth) : SliceFamGood :=
  SFG.sliceFamGood_of hGf hRP hPS hPt SFG.point_mem_unitary_group SFG.ckExt_proof

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateTopBound
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem germ_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Vec : C.LPt → H) (b s : ℕ) (hs : 2 ≤ s) (hbs : b + s - 1 = S.G.r + 1) (h : C.LPt)
    (x D : ℂ) (hD : D ≠ 0) :
    utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
        mainD s (betaL S) 1 (fun z => (fun _ => (1 : ℂ)) z • btOf s (KB.dlB S b s) Vec h z) x D =
      ∑ j ∈ Finset.insertNone (G.rootSet s D), coJ S b s x j • Vec (ptJ s h x D j) := by
  rw [Finset.sum_insertNone, hbs, sub_eq_add_neg]
  have hz : ∀ z ∈ G.rootSet s D, z ≠ 0 := by
    intro z hz h0
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [h0, zero_pow (by omega)] at hz
    exact hD hz.symm
  congr 1
  · simp only [utOf, vOf, ptX, coJ, ptJ, smul_smul, List.append_assoc, List.singleton_append]
    push_cast
    rfl
  · unfold mainD
    rw [one_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hzm => ?_
    simp only [btOf, if_neg (hz z hzm), one_smul, coJ, ptJ, smul_smul, neg_smul, one_mul]

end

end Formalism.FourierDecayAlt.P.GermRateSplit

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Formalism.FourierDecayAlt.P.GermRateSplit Finset
open scoped ComplexConjugate InnerProductSpace

theorem germ_rate_top_bound : Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB := by
  intro hA Cb
  obtain ⟨c1, hc1⟩ := GermFibreKernels.cutSeq_cpt Cb
  refine ⟨c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hF := hc1 c1 le_rfl E Wp Wq S p f χ A₀ hB n
  intro ε hε b s hb hs hbs a ha H _ _ _ Vec hVec
  refine ⟨1, fun _ => 1, by simp, fun _ => by simp, continuousOn_const, ?_⟩
  intro h hsz K hK hK0
  have hbs' : b + s = S.G.r + 2 := hbs
  have hb1 : b + s - 1 = S.G.r + 1 := by omega
  obtain ⟨I, hI, c, Fi, L, hc, hFi, hgram⟩ :=
    gN_top_gram hB (PBASM.cutSeq S p f χ n) (fun v ε hε => hF v ε hε) v ε hε a ha
  choose Ci hCi using fun i => top_core hB v (Fi i) (hFi i) a.length b s hb hs hbs' h hsz K hK hK0
  refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  rw [germ_sum (PBL.setC S p (PBASM.cutSeq S p f χ n)) Vec b s hs hb1 h x D hD0]
  have hk : ∀ j ∈ Finset.insertNone (G.rootSet s D), ∀ l ∈ Finset.insertNone (G.rootSet s D),
      KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a (ptJ s h x D j) (ptJ s h x D l) =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length (ptJ s h x D l) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D l))),
          (omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))⟫_ℂ := by
    intro j _ l _
    rw [hb1]
    exact hgram _ _
  have h2 := norm_sum_le_of_gram (fun P Q => KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a P Q)
    Vec hVec c hc (fun i P => (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P)))
    (Finset.insertNone (G.rootSet s D)) (ptJ s h x D) hk (coJ S b s x)
  refine h2.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : ∑ j ∈ Finset.insertNone (G.rootSet s D), conj (coJ S b s x j) •
        ((omN S a.length (ptJ s h x D j) : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))) =
      L i (∑ j ∈ Finset.insertNone (G.rootSet s D), (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) •
        (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul]
  rw [e]
  have h3 := hCi i x hx D hD
  have hsq := Real.sqrt_nonneg (c i)
  calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j)))‖
      ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s D),
        (conj (coJ S b s x j) * (omN S a.length (ptJ s h x D j) : ℂ)) • (p v).V (Fi i) (PBL.stdS S (ptJ s h x D j))‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
    _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
    _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadLetterOfMinusPos
section
namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_minusPos (hMP : MinusPosOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_rest Formalism.FourierDecayAlt.P.LevelPointCoordinates.left_rule_level_point torus_action_x0 Formalism.FourierDecayAlt.P.star_rule_x0 star_torus_x0
    Formalism.FourierDecayAlt.P.LevelPointCoordinates.plusPosOfParts Formalism.FourierDecayAlt.P.plus_zero_of_parts hMP Formalism.FourierDecayAlt.P.minus_zero_of_parts

end Formalism.FourierDecayAlt.P.CutHL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem properE {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (e : p + ρ = n) (Cs : Set (B.Mat k n)) (hCs : IsCompact Cs) :
    PartialBesselProperness.Proper Bj B0 e Cs (domP k n p B0.z B0.z') := by
  subst e
  exact properA Bj B0 (fun q hq => leviElement_mem_GV q hq)
    (fun y hy hyG => levi_move_into_big_cell k p ρ B0.z B0.z' B0.z_mem B0.z'_mem y hy hyG) Cs hCs

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

end Formalism.FourierDecayAlt.P.PBQ

namespace Formalism.FourierDecayAlt.P

theorem proper_left_variables_domain : PBQ.ProperDomP := by
  intro Wp Wq _ _ _ _ _ _ P p j hj Cs hCs
  exact PBQ.properE (p.T.bs j) p.T.base _ Cs hCs

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishKr
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vanish_kr (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    {H : B.Mat k n → (Wq →L[ℂ] Wp)} {Cs : Set (B.Mat k n)} (hH : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0)
    {U : Set (B.Mat k n)} (hP : Proper Bj B0 e Cs U) : VanishL Bj e (PBG.Kr B0 H) U := by
  intro y hy
  obtain ⟨V, hV, K, hK, hVK⟩ := hP y hy
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, K, hK, fun g hg hgG x hx hxK => ?_⟩
  rw [Formalism.FourierDecayAlt.P.PBG.kr_eq]
  rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.PBG.ae_inR B0] with ξ hξ
  rw [Formalism.FourierDecayAlt.P.PBG.rho_pR]
  have hG : sE Bj e x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k n :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (sE_GV Bj e x) hgG) hξ.2.1) hξ.1.1
  have hC := hVK g (interior_subset hg) hgG x hx hxK ξ hξ
  rw [hH _ hG hC]
  simp

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordSmoothPartialBesselInduction
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselWordSmoothness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBQ

def ProperDomPH : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem smooth_pbT (hP : ProperDomPH) (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (j : ℕ) (hj : j ≤ P.r) (hF : KB.CptCoef p.T.base F) :
    Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z') (pbT p j hj F) := by
  obtain ⟨hck, ⟨R, hR⟩, -⟩ := hF
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hz : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → F g = 0 := fun g hg hgC => by
    by_contra h; exact hgC (hR g hg h)
  have hzl : p.T.base.z = D.castV (by omega : j + (P.r - j) = P.r) (liftVec P.k j (P.r - j) (p.T.bs j).z) :=
    (p.T.z_lev j hj).symm
  refine Formalism.FourierDecayAlt.P.PBG.smoothLev_of_loc fun x hx => ?_
  exact Formalism.FourierDecayAlt.P.partial_bessel_smooth_compact_support P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base (by omega) hzl F _ hck hCs hz
    _ (isOpen_domP P.k P.r j p.T.base.z p.T.base.z') (hP Wp Wq P p j hj _ hCs) x hx.2 hx.1.1

theorem word_smooth_partial_bessel_induction (hP : ProperDomPH) (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (j : ℕ) (hj : j + 1 ≤ P.r) (hF : KB.CptCoef p.T.base F) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z')
        (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w e)
  | [], _ => smooth_pbT hP P p F j (by omega) hF
  | l :: w, e => by
    show Q.SmoothLev P.k P.r 0 _ (D.vLet P.k P.r p.T.base.z p.T.base.z' j (by omega) l (e 0)
      (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w fun a => e a.succ))
    exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.smooth_vLet _ _ j (by omega) l (e 0) (isOpen_domP P.k P.r j p.T.base.z p.T.base.z')
      (word_smooth_partial_bessel_induction hP P p F j hj hF w _) (fun g hg => hg.1 ⟨j, by omega⟩ (show j ≤ j from le_rfl) (show j ≤ P.r by omega))

end

theorem wordSmooth_of (hP : ProperDomPH) : CutHB.WordSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w hF _ e
  exact word_smooth_partial_bessel_induction hP P p F j hj hF w e

end Formalism.FourierDecayAlt.P.PartialBesselWordSmoothness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnlyOfLeviCurve
section
namespace Formalism.FourierDecayAlt.P

theorem z_only_of_levi_curve (hC : WirtingerOperators.CurveLevi) (hH : WirtingerOperators.HpartLevi) : LevelPointCoordinates.ZOnly :=
  WirtingerOperators.zOnly_of_parts hC hH xi_coefficient xi_coefficient_vector xiMem_statement xi_smooth
    right_derivative_operator_class wirtinger_slice_smooth

end Formalism.FourierDecayAlt.P
end

