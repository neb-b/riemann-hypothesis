module

public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SesquilinearLevelZeroPairing

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadContinuityAtZeroOfStandard
section
namespace Formalism.FourierDecayAlt.P.TBBx3

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecCutAt_of_one (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hχ : ∀ x, 1 ≤ x → χ x = 1) : TBB.VecCutAt p χ F := by
  intro ε hε γ hγ hle
  have hle0 : ε ≤ D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hle
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF]
    have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose hγ h'.choose_spec.2.1
    have hle' : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hle0
    rw [hχ _ ((one_le_div hε).mpr hle'), Complex.ofReal_one, one_smul]
  · rfl
  · rfl

theorem hsInner_self_re_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ (B.hsInner A A).re := by
  unfold B.hsInner
  have h := inner_self_nonneg (𝕜 := ℂ) (x := B.hsVec A)
  simpa using h

theorem rr_top_re_nonneg (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (h : C.LPt) (hi : P.r < i) : 0 ≤ (p.RR F i w h h).re := by
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt h i ∧ D.IsLocPt h i
  · rw [dite_eq_left h1, dite_eq_right (by omega)]
    by_cases h2 : i = P.r + 1
    · rw [if_pos h2]
      by_cases h3 : w = []
      · rw [if_pos h3]
        exact hsInner_self_re_nonneg _
      · rw [if_neg h3]
        unfold Top.topOf
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun e _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun ρ _ => ?_
        rw [Complex.re_ofReal_mul]
        exact mul_nonneg (mul_self_nonneg _) (hsInner_self_re_nonneg _)
    · rw [if_neg h2]
      simp
  · rw [dite_eq_right h1]
    simp

theorem posAt_of_forms (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hnn : ∀ y, 0 ≤ nn y)
    (hform : ∀ (j : ℕ) (w : List C.Letter) (h : C.LPt), j ≤ P.r → TBB.AdmW P p.l0 Y w → w.length ≤ N →
      0 ≤ (p.RR F j w h h).re) : TBB.PosAt p nn F Y N := by
  intro i w h hw hN
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul]
  apply mul_nonneg
  · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    unfold TBB.normC
    apply List.prod_nonneg
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨l, _, rfl⟩ := ha
    exact hnn _
  · by_cases hi : i ≤ P.r
    · exact hform i w h hi hw hN
    · exact rr_top_re_nonneg p F i w h (by omega)

theorem ew_zero_nil (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    TBB.Ew p nn G 0 w [] = (p.RR G 0 w [] []).re / TBB.normC nn w := by
  have h1 : ∀ TT : ℝ, TBB.nPt P.k P.r TT [] = 1 := fun TT => by simp [TBB.nPt, C.nAux]
  unfold TBB.Ew TBB.NP
  simp only [h1, Real.sqrt_one, one_mul]
  rw [Complex.re_ofReal_mul, one_div, inv_mul_eq_div]

theorem limZeroAt_of_limits (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F) :
    TBB.LimZeroAt p nn χ F Y N κ₀ := by
  intro w hw hN
  obtain ⟨sz, hsz0, hszn, hlim⟩ := hE w hw hN
  have hEw : ∀ ε, TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re / TBB.normC nn w := fun ε => ew_zero_nil p nn _ w
  have hlim2 : Tendsto (fun ε => ENNReal.ofReal (TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (sz * (B.beta p.T.base F F).re / TBB.normC nn w))) := by
    simp only [hEw]
    exact ENNReal.tendsto_ofReal (hlim.div_const _)
  rw [hlim2.limsup_eq]
  refine le_trans ?_ hB
  rw [ENNReal.ofReal_le_ofReal_iff']
  have hn0 : 0 ≤ TBB.normC nn w := le_trans hsz0 hszn
  by_cases hb : 0 ≤ (B.beta p.T.base F F).re
  · left
    rcases hn0.lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]
      calc sz * (B.beta p.T.base F F).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re :=
            mul_le_mul_of_nonneg_right hszn hb
        _ = (B.beta p.T.base F F).re * TBB.normC nn w := mul_comm _ _
    · rw [← hzero, div_zero]
      exact hb
  · right
    push_neg at hb
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsz0 hb.le) hn0

end

end Formalism.FourierDecayAlt.P.TBBx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem vector_truncation_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hχ : ∀ x, 1 ≤ x → χ x = 1) : Formalism.FourierDecayAlt.TBB.VecCutAt p χ F := by
  exact TBBx3.vecCutAt_of_one p χ F hχ

theorem limit_zero_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, Formalism.FourierDecayAlt.TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ Formalism.FourierDecayAlt.TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * Formalism.FourierDecayAlt.TBB.jN2 p F) :
    Formalism.FourierDecayAlt.TBB.LimZeroAt p nn χ F Y N κ₀ := by
  exact TBBx3.limZeroAt_of_limits p nn χ F Y N κ₀ hE hB

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Filter

noncomputable section

section om

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem maxpow_le_onepow {x y a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ (-a) ≤ (max 1 y) ^ (-a) := by
  refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
  exact max_le (by linarith) (by linarith)

theorem continuous_lowRow (n : ℕ) : Continuous (fun a : Fin n → ℂ => lowRow a) := by
  unfold lowRow
  exact P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const

theorem continuous_blkU (n : ℕ) :
    Continuous (fun p : (UT n → ℂ) × (Fin n → ℂ) => blk (upper p.1) p.2 0 1) :=
  P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const

theorem continuous_orbM (n : ℕ) (t c : ℂ) : Continuous (orbM n t c) := by
  unfold orbM
  refine Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_
  exact (continuous_blkU n).comp (continuous_snd)

theorem integrable_blockIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 2) → V) (t c : ℂ) (ht : t ≠ 0) (K a : ℝ)
    (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) (hc : ∀ p, ContinuousAt Φ (orbM (m + 1) t c p))
    (hb : ∀ p, ‖Φ (orbM (m + 1) t c p)‖ ≤ K * (1 + ‖orbM (m + 1) t c p‖) ^ (-a)) :
    Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (orbM (m + 1) t c 0))]
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a) := by
    intro p
    rw [P.OrbitTailEstimates.norm_blockIntegrand]
    refine (hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0
  obtain ⟨k, hk⟩ := P.G7.muBlock_eq β (m + 1)
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a := by
    rw [P.OrbitTailEstimates.finrank_block_cast]; exact ha
  have hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1)) := by
    rw [hk]; exact (P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal
  have hJ := P.G7.jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
    unfold blockIntegrand
    refine Continuous.smul ?_ ?_
    · have h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1) := by
        unfold G.subSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))
      have h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1) := by
        unfold G.superSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))
      exact ((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)
    · exact continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt
  exact (hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)

theorem integrable_longIntegrand (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) (hz : z ≠ 0) (K a : ℝ)
    (ha : (Module.finrank ℝ (UT (n + 1) → ℂ) : ℝ) < a)
    (hc : ∀ v, ContinuousAt Φ (P.JCTx6.Pos.Zv n z v))
    (hb : ∀ v, ‖Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (1 + ‖P.JCTx6.Pos.Zv n z v‖) ^ (-a)) :
    Integrable (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v))
      (muPi U.betaU (UT (n + 1))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]
  have hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v) := by
    show Continuous (fun v : UT (n + 1) → ℂ =>
      ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))
    exact continuous_const.matrix_mul P.Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v)) :=
    continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt
  have hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v))) := by
    have h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v) := by
      unfold superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)
    exact (P.G7.continuous_psi _).comp h1
  have hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤
      K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]
    refine (hb v).trans ?_
    have := mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK
    rw [← mul_assoc] at this
    exact this
  rw [P.Dx2.SL.muPi_betaU]
  apply Integrable.smul_measure_nnreal
  exact ((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono'
    (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

theorem clm_omBlock [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (t c : ℂ) (hI : Integrable (blockIntegrand β n Φ t c) (muBlock β n)) :
    L (OmBlock β n Φ t c) = OmBlock β n (fun Z => L (Φ Z)) t c := by
  unfold OmBlock
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [blockIntegrand, L.map_smul]

theorem clm_omLong [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (z : ℂ) (hI : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1)))) :
    L (OmLong β n Φ z) = OmLong β n (fun Z => L (Φ Z)) z := by
  unfold OmLong
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [L.map_smul]

end om

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableSliceAppendSingle
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem point_size_append_single (h : C.LPt) (c : ℂ) : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := by
  rw [Dx2.SL.ptSize_append]

theorem integrable_slice_append_single {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h : C.LPt) (c : ℂ)
    (hle : D.ptSize (h ++ [(1, c)]) ≤ r) (hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])))
    (γ' : B.Mat k (r - D.ptSize (h ++ [(1, c)])))
    (hI : Integrable (JCTx6.gInt k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
        (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
        (D.castF (by have := point_size_append_single h c; omega) F) γ')
      (JCTx6.muG k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h))) :
    Integrable (fun ξ : U.Xi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) =>
        U.psiStar k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) (D.castV (by omega) z)
            (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))
            (D.ptDiag (h ++ [(1, c)])) ξ (fun a => a.elim0) γ'))
      (U.muXi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))) := by
  have hP : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := point_size_append_single h c
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (Dx2.SL.isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(1, c)]) a).val := by
    intro a
    rw [hspec a, Dx2.SL.partner_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      Dx2.SL.dP (n := 0) (D.ptDiag h) c (Fin.cast hP a) = D.ptDiag (h ++ [(1, c)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [Dx2.SL.scal_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.dP, Fin.addCases_right]

  have hσ' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      (D.ptPerm (h ++ [(1, c)]) (Fin.cast hP.symm b)).val = ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) b).val := by
    intro b
    have := hσ (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have hd' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      D.ptDiag (h ++ [(1, c)]) (Fin.cast hP.symm b) = Dx2.SL.dP (n := 0) (D.ptDiag h) c b := by
    intro b
    have := hd (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have h1 := JCTx6.Int.orbit_slice_integrable k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z') E
    (D.castF (by have := point_size_append_single h c; omega) F) γ' hI
  have h2 := (Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(1, c)])) hP.symm _ _ hσ' _ _ hd'
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
    (D.castF (by have := point_size_append_single h c; omega) F) γ').1 h1
  simpa only [Dx2.SL.castV_castV, Dx2.SL.castF_castF] using h2

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PictureMemLevelZeroClass
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Tower

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

def IsPic (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
    (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) F) y.1 y.2

theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Φ Ψ : RadSp k r z z' π π')
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · exact h _ hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

theorem resG_JF_zero {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (i : Fin (r + 1)) :
    resG k r i (B.JF Bs (fun _ => (0 : Wq →L[ℂ] Wp))) = 0 := by
  funext c g
  simp [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero]

end Tower

section Cls

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

end Cls

section Words

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {S : Type}

theorem wordOK_gen (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hOK : P.OK) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (hq : st.q = M.qC P)
    (hinv : st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}) (u : List (Letter ℂ S))
    (hnd : (u.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hpt : ∀ l ∈ u, ∃ Y : ℝ, l.pt = (Y : ℂ) ∧ I.OnCut P.u P.u' l0 Y)
    (hsep : u.Pairwise fun l l' => 2 < |l.pt.re - l'.pt.re|) : WordOK P z z' π π' st l0 u := by
  refine ⟨⟨hnd, ?_, ?_, ?_⟩, ?_, hsep⟩
  · intro l hl
    obtain ⟨Y, e, -⟩ := hpt l hl
    rw [e]; exact Complex.conj_ofReal Y
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    have hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ ((Y + e : ℝ) : ℂ) ≠ 0 :=
      fun e h1 h2 ρ => Formalism.FourierDecayAlt.P.JCTx5.xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ
    · rw [hq]; simpa using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)
    · rw [hq]; simpa [sub_eq_add_neg] using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)
  · refine hsep.imp fun {l l'} h n hn e => ?_
    have hre : l.pt.re - l'.pt.re = (n : ℝ) := by
      have := congrArg Complex.re e
      simpa using this
    have h2 : |(n : ℝ)| ≤ 2 := by exact_mod_cast hn
    rw [hre] at h
    linarith
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    exact ⟨by simp, by simpa using hc⟩

end Words

end

end Formalism.FourierDecayAlt.P.PBF
end

