module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0119

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_sgs (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) (g : B.Mat k r) :
    Gf k r D.z D.z' (B.sgs p g) = Gf k r D.z D.z' g := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hn1 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Q.Nlev k r 0 := by
    refine ⟨Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn, ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact (Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn).1
  have hn2 : (Matrix.of p.2.2 : B.Mat k r) ∈ Q.Nlev k r 0 := by
    refine ⟨hn', ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact hn'.1
  have e1 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh))
    (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z' hh') ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * g * Matrix.of p.2.2)
  have e2 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z hn1)
    (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z' hn2) g
  unfold B.sgs
  rw [← e2, ← e1]
  congr 1
  simp only [mul_assoc]

theorem sgs_mem (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {g : B.Mat k r}
    (hg : g ∈ B.GV k r) : B.sgs p g ∈ B.GV k r := by
  rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)) hg) (Formalism.FourierDecayAlt.P.B5.inSS_right D hp)

theorem sgs_continuous (p : B.SS k r) : Continuous (B.sgs p : B.Mat k r → B.Mat k r) := by
  unfold B.sgs
  exact (((continuous_const : Continuous fun _ : B.Mat k r =>
    (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹).matrix_mul continuous_id).matrix_mul
    continuous_const).matrix_mul continuous_const

theorem suppIn_rho (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : B.SuppIn (B.GPos D) F) : B.SuppIn (B.GPos D) (B.rho D p F) := by
  intro x hx
  have hxG : x ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
  have hsub : {g | g ∈ B.GV k r ∧ B.rho D p F g ≠ 0} ⊆ B.sgs p ⁻¹' {g | g ∈ B.GV k r ∧ F g ≠ 0} := by
    intro y hy
    refine ⟨sgs_mem D hp hy.1, fun h0 => hy.2 ?_⟩
    unfold B.rho
    rw [h0]
    simp
  have h1 : x ∈ B.sgs p ⁻¹' closure {g | g ∈ B.GV k r ∧ F g ≠ 0} :=
    (sgs_continuous p).closure_preimage_subset _ (closure_mono hsub hx)
  have h2 := hF h1
  refine ⟨hxG, ?_⟩
  have := h2.2
  rwa [gf_sgs D hp] at this

variable [FiniteDimensional ℂ Wq]

theorem ckOn_opAdj (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hs : B.SmoothCoef (B.GPos D) Θ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) (hFs : B.SuppIn (B.GPos D) F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := by
  unfold B.opAdj
  refine Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum Θ
    (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) (fun T hT => ?_)
  exact Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF hFs)
    T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)))

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

theorem adjoint_continuity_holds : AdjCont := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs f hf _ hfs p hp
  exact ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_opAdj D Θ hs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (suppIn_rho D hp hfs)),
    Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp (ckOn_opAdj D Θ hs hf hfs))⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACSmooth
section
open MeasureTheory Topology Matrix
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def linM {k r : ℕ} (A Bb : B.Mat k r) : Mt k r →ₗ[ℝ] Mt k r :=
  ((LinearMap.mulLeft ℝ A).comp (LinearMap.mulRight ℝ Bb) : B.Mat k r →ₗ[ℝ] B.Mat k r)

theorem linM_apply {k r : ℕ} (A Bb : B.Mat k r) (v : Mt k r) :
    (Matrix.of (linM A Bb v) : B.Mat k r) = A * Matrix.of v * Bb := by
  show A * ((Matrix.of v : B.Mat k r) * Bb) = _
  rw [Matrix.mul_assoc]

theorem aCSmooth_of_proper (hP : ACProper) : ACSmooth := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc hφs g₀ hg₀

  obtain ⟨ε₀, hε₀, hball⟩ :=
    Metric.mem_nhds_iff.1 ((Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z').mem_nhds hg₀.2)
  have hε : 0 < ε₀ / 2 := by positivity
  have hCb : Metric.closedBall g₀ (ε₀ / 2) ⊆ Q.OmPlus k r D.z D.z' := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  have hC'c : IsCompact (Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r) :=
    (isCompact_closedBall g₀ (ε₀ / 2)).inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  have hC'O : Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r ⊆ JF.Om k r D.z D.z' := fun x hx => ⟨hx.2, hCb hx.1⟩
  obtain ⟨P, hPc, hPp⟩ := hP k r Wp Wq D (tsupport φ₀) _ hφc hC'c hC'O

  set Am : B.SS k r → B.Mat k r := fun p =>
    (Hpk k r * (Matrix.of p.1.1 : B.Mat k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of p.1.2 : B.Mat k r)ᴴ * Hpk k r)
    with hAm
  set Bm : B.SS k r → B.Mat k r := fun p => (Matrix.of p.2.2 : B.Mat k r) * Matrix.of p.2.1 with hBm
  have hsgs : ∀ p, D.inSS p → ∀ g, B.sgs p g = Am p * g * Bm p := by
    intro p hp g
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _
    rw [Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.1.1, Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.2.1.1]
    simp only [hAm, hBm, Matrix.mul_assoc]
  have hof : Continuous (fun ν : Mt k r => (Matrix.of ν : B.Mat k r)) := continuous_id
  have hAc : Continuous Am := by
    have h1 : Continuous (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)) := hof.comp continuous_fst.fst
    have h2 : Continuous (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)) := hof.comp continuous_fst.snd
    exact ((continuous_const.mul h1.matrix_conjTranspose).mul continuous_const).mul
      ((continuous_const.mul h2.matrix_conjTranspose).mul continuous_const)
  have hBc : Continuous Bm := by
    have h3 : Continuous (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) := hof.comp continuous_snd.snd
    have h4 : Continuous (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) := hof.comp continuous_snd.fst
    exact h3.mul h4
  have hcont : Continuous (fun p : B.SS k r => B.gN (Am p) * B.gN (Bm p)) :=
    (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hAc).mul (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hBc)
  obtain ⟨M₁, hM₁⟩ := hPc.exists_bound_of_continuousOn hcont.continuousOn
  set L : B.SS k r → (Mt k r →L[ℝ] Mt k r) := fun p => LinearMap.toContinuousLinearMap (linM (Am p) (Bm p))
    with hLdef
  have hL : ∀ p (v : Mt k r), (Matrix.of (L p v) : B.Mat k r) = Am p * Matrix.of v * Bm p := fun p v =>
    linM_apply (Am p) (Bm p) v
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := by positivity
  set ML : ℝ := nn * max M₁ 0 with hML
  have hML0 : 0 ≤ ML := mul_nonneg hnn0 (le_max_right _ _)
  have hLn : ∀ p ∈ P, ‖L p‖ ≤ ML := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ hML0
    intro v
    have e1 : ‖L p v‖ = ‖(Matrix.of (L p v) : B.Mat k r)‖ := rfl
    have e2 : ‖v‖ = ‖(Matrix.of v : B.Mat k r)‖ := rfl
    rw [e1, e2, hL]
    set g : B.Mat k r := Matrix.of v
    have hgA := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Am p)
    have hgB := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Bm p)
    have hgg := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg g
    have hgn : B.gN g ≤ nn * ‖g‖ :=
      Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_le_of_ent g ‖g‖ (norm_nonneg _) (fun i j => Matrix.norm_entry_le_entrywise_sup_norm g)
    have hAB : B.gN (Am p) * B.gN (Bm p) ≤ max M₁ 0 := by
      have := hM₁ p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgA hgB)] at this
      exact this.trans (le_max_left _ _)
    calc ‖Am p * g * Bm p‖ ≤ B.gN (Am p * g * Bm p) := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN _
      _ ≤ B.gN (Am p * g) * B.gN (Bm p) := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Am p) * B.gN g) * B.gN (Bm p) :=
          mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) hgB
      _ = (B.gN (Am p) * B.gN (Bm p)) * B.gN g := by ring
      _ ≤ max M₁ 0 * (nn * ‖g‖) := mul_le_mul hAB hgn hgg (le_max_right _ _)
      _ = ML * ‖g‖ := by rw [hML]; ring

  set φ₁ : Mt k r → ℝ := fun v => φ₀ (Matrix.of v) with hφ₁def
  have hφ₁ : ContDiff ℝ ∞ φ₁ := hφ
  have hφ₁c : HasCompactSupport φ₁ := hφc
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ i φ₁ x‖ ≤ K := fun i =>
    (hφ₁.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hφ₁c.iteratedFDeriv i)
  choose K hKb using hK

  set F : B.SS k r → Mt k r → ℝ := fun p y => P.indicator (fun p => φ₁ (L p y)) p with hF
  have hFin : ∀ p ∈ P, F p = φ₁ ∘ (L p) := fun p hp => by
    funext y; simp [hF, hp]
  have hFout : ∀ p ∉ P, F p = fun _ => 0 := fun p hp => by
    funext y; simp [hF, hp]

  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨D.haarW.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨D.haarN.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨D.haarW'.finite_compact⟩
  have : IsFiniteMeasureOnCompacts (D.μW.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts (D.μW'.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts D.μSS := by
    show IsFiniteMeasureOnCompacts ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
    infer_instance
  have hPfin : D.μSS P ≠ ⊤ := (hPc.measure_lt_top (μ := D.μSS)).ne
  have hPm : MeasurableSet P := hPc.isClosed.measurableSet
  have hFm : ∀ y, AEStronglyMeasurable (fun p => F p y) D.μSS := by
    intro y
    have hc : Continuous (fun p => φ₁ (L p y)) := by
      have : (fun p => φ₁ (L p y)) = fun p => φ₀ (Am p * Matrix.of y * Bm p) := by
        funext p; simp only [hφ₁def]; rw [hL]
      rw [this]
      exact hφ.continuous.comp ((hAc.mul continuous_const).mul hBc)
    exact (hc.measurable.indicator hPm).aestronglyMeasurable
  have hsm : ContDiffOn ℝ ∞ (fun y => ∫ p, F p y ∂D.μSS) (Metric.ball (Matrix.of.symm g₀ : Mt k r) (ε₀ / 2)) := by
    rw [contDiffOn_infty]
    intro N
    set Kt : ℝ := (∑ i ∈ Finset.range (N + 1), |K i|) * (max ML 1) ^ N with hKt
    have hb : Integrable (P.indicator fun _ => Kt) D.μSS :=
      (integrableOn_const hPfin).integrable_indicator hPm
    refine (Formalism.FourierDecayAlt.P.Ux10.pint Metric.isOpen_ball (P.indicator fun _ => Kt) hb N ℝ F ?_ (fun y _ => hFm y) ?_).1
    · intro p
      by_cases hp : p ∈ P
      · rw [hFin p hp]
        exact (hφ₁.comp (L p).contDiff).contDiffOn.of_le (mod_cast le_top)
      · rw [hFout p hp]; exact contDiffOn_const
    · intro i hi y _ p
      by_cases hp : p ∈ P
      · rw [hFin p hp, ContinuousLinearMap.iteratedFDeriv_comp_right (L p) hφ₁ y (mod_cast le_top)]
        simp only [Set.indicator_of_mem hp]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have h1 : ‖iteratedFDeriv ℝ i φ₁ (L p y)‖ ≤ ∑ j ∈ Finset.range (N + 1), |K j| :=
          (hKb i _).trans ((le_abs_self _).trans
            (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
        have h2 : ‖L p‖ ^ i ≤ (max ML 1) ^ N :=
          (pow_le_pow_left₀ (norm_nonneg _) ((hLn p hp).trans (le_max_left _ _)) i).trans
            (pow_le_pow_right₀ (le_max_right _ _) hi)
        exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _)
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
      · rw [hFout p hp, iteratedFDeriv_fun_zero]
        simp [Set.indicator_of_notMem hp]
  refine ⟨Metric.ball g₀ (ε₀ / 2), fun g => ∫ p, F p (Matrix.of.symm g) ∂D.μSS, Metric.isOpen_ball,
    Metric.mem_ball_self hε, hsm, ?_⟩
  intro g hg hgG
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · have e : φ₁ (L p (Matrix.of.symm g)) = φ₀ (Am p * g * Bm p) := by
      simp only [hφ₁def]; rw [hL]; rfl
    simp only [hF, Set.indicator_of_mem hpP, e, hsgs p hp g]
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPp p hp g ⟨Metric.ball_subset_closedBall hg, hgG⟩ (subset_tsupport _ hne))
    simp [hF, hpP, h0]

theorem averaging_smoothness_holds : ACSmooth := aCSmooth_of_proper averaging_properness_holds

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def colsVm (k r m : ℕ) (j : Fin m) : Fin (2 * r + k + 1) := ⟨2 * r + k - (r - 1 - j.val), by omega⟩

def kvM (k r m : ℕ) (w : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  qminorOp (Q.EH k r) (colsVm k r m) (colsVm k r m) w F

def kvTop (k r : ℕ) (y : ℂ) : ℂ := (y - ((2 * r + k : ℕ) : ℂ) / 2) + ((r : ℕ) : ℂ) - 1

def pbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then pbOp ⟨i, h⟩ f else 0

def cbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbOp ⟨i, h⟩ f else 0

def cbiN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbiOp ⟨i, h⟩ f else 0

def kvP (r : ℕ) (w : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (fun f => f, fun _ => 0)
  | m + 1 =>
    (fun f => (kvP r w m).1 (fun c => (w - (m : ℂ)) • f c - pbN r (r - m - 1) f c) -
        cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f)),
      (kvP r w m).1)

def kvC (r : ℕ) (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := (kvP r w m).1 f

def gaugeF (k r : ℕ) (c : Fin r → ℂ) : ℂ := Q.resG k r (Fin.last r) (fun _ => (1 : ℂ)) c 1

end defs

def TVCoef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g)

def TVGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c

def TVCrd : Prop :=
  ∀ (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (Φ : (Fin r → ℂ) → X)
    (U : Set (Fin r → ℂ)) (c : Fin r → ℂ), IsOpen U → U ⊆ OmX r → c ∈ U →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => gaugeF k r c' • Φ c') U →
      gaugeF k r c • kvC r (kvTop k r y) r Φ c = (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c


open scoped ContDiff in
theorem jDACapTodaV_of_parts (h1 : TVCoef) (h2 : TVGrp) (h3 : TVCrd) : JDACapTodaV := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have e1 := h1 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have e2 := h2 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp (s := U') hemb.contDiffOn (fun c' hc' => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := h3 P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, if_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolW
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_lieW {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hW : ∀ X ∈ lieOf (UWset k r z), (Matrix.trace (ζ * X)).re = 0)
    (u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  refine herm_zero_of_trace hζ u v (hW _ (xuv_lieW z u v hu hv huz hvz)) (hW _ ?_)
  refine xuv_lieW z u _ hu (inWb_smul _ hv) huz ?_
  rw [herm_smul_left, hvz, mul_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExistence
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem frame_existence : FrameEx := fun _ _ _ hz hT => Qx8.frame_exists hz hT

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupVectorSpace
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_vector_space : GVGrp := by
  intro k r
  refine ⟨⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩, fun g₀ hg₀ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, smul_add, ← add_smul]
    norm_num
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_add, ← add_smul]
    norm_num
  · have hdet : IsUnit g₀.det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hg₀
    refine ⟨Matrix.nonsing_inv_mul g₀ hdet, fun h hh => ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul hg₀ hh,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.PBM.GV_inv_mem g₀ hg₀) hh, ?_⟩⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hdet, Matrix.one_mul]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOf
section
namespace Formalism.FourierDecayAlt.P

theorem pb_headTop_of (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) : KB.HeadTop :=
  head_top_of_radial_exhaustion hU5 hPic head_weight_at

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDomainIsDomain
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem positive_domain_is_domain : IsDomOmPlus := fun _ _ _ _ hz hz' =>
  Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus hz hz'

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

