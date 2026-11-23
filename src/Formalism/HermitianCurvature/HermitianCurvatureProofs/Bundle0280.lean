module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0279
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOneLetterDens
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0264
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0269
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDomCutInt
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section general

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jgq_continuousOn (D : B.RealPlaceData k r Wp Wq) {A : ℝ} {H : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hT : JF.TransportedAlt k r A 0) (hH : B.InCC A 0 H) :
    ContinuousOn (fun q => B.JF D H (B.gq D q)) (JF.QDom k r D.z D.z') := by
  exact (Formalism.FourierDecayAlt.Final.jf_jqSmooth k r Wp Wq D A 0 H hT hH).continuousOn

theorem aesm_weight_smul (D : B.RealPlaceData k r Wp Wq) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin r → ℂ) × ℂ → E} (hc : ContinuousOn g (JF.QDom k r D.z D.z')) :
    AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q) volume := by
  set s := JF.QDom k r D.z D.z' with hs_def
  have hs : MeasurableSet s := by
    have hseq : s = (⋂ a : Fin r, {q : (Fin r → ℂ) × ℂ | q.1 a ≠ 0}) ∩
        {q | Tz k r D.z * Tz k r D.z' < Complex.normSq q.2} := by
      ext q
      simp [hs_def, JF.QDom]
    rw [hseq]
    refine IsOpen.measurableSet (IsOpen.inter (isOpen_iInter_of_finite fun a => ?_) ?_)
    · exact isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
    · exact isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  have contW : Continuous (fun q : (Fin r → ℂ) × ℂ => (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) *
      (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') ^ (k - 1)) := by
    first | fun_prop | continuity
  have hw : ContinuousOn (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q) s := by
    refine contW.continuousOn.congr fun q hq => ?_
    unfold bcWeight
    rw [if_pos hq.2.le]
  have h1 : AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q)
      (volume.restrict s) := (hw.smul hc).aestronglyMeasurable hs
  have h2 := (aestronglyMeasurable_indicator_iff hs).mpr h1
  refine h2.congr ?_
  have hN1 : ∀ a : Fin r, volume {q : (Fin r → ℂ) × ℂ | q.1 a = 0} = 0 := by
    intro a
    have h0 : volume {x : Fin r → ℂ | x a = 0} = 0 := by
      have he : {x : Fin r → ℂ | x a = 0} = Function.eval a ⁻¹' {0} := rfl
      rw [he, MeasureTheory.volume_pi]
      first
        | exact MeasureTheory.Measure.pi_eval_preimage_null _ (measure_singleton 0)
        | exact MeasureTheory.Measure.pi_eval_preimage_null (measure_singleton 0)
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_fst h0
  have hN2 : volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = Tz k r D.z * Tz k r D.z'} = 0 := by
    have hsph : volume (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r D.z * Tz k r D.z'))) = 0 := by
      first
        | exact MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) _
        | exact MeasureTheory.Measure.addHaar_sphere (0 : ℂ) _
    have h0 : volume {z : ℂ | Complex.normSq z = Tz k r D.z * Tz k r D.z'} = 0 := by
      refine measure_mono_null (fun z hz => ?_) hsph
      simp only [Set.mem_setOf_eq] at hz
      rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_snd h0
  have hA : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), ∀ a : Fin r, q.1 a ≠ 0 :=
    ae_all_iff.mpr fun a => ae_iff.mpr (by simpa using hN1 a)
  have hB : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), Complex.normSq q.2 ≠ Tz k r D.z * Tz k r D.z' :=
    ae_iff.mpr (by simpa using hN2)
  filter_upwards [hA, hB] with q hqa hqb
  classical
  by_cases hq : q ∈ s
  · simp [Set.indicator_apply, hq]
  · simp only [Set.indicator_apply, hq, if_false]
    have hlt : Complex.normSq q.2 < Tz k r D.z * Tz k r D.z' := by
      have hn : ¬ (Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) := fun h => hq ⟨hqa, h⟩
      exact lt_of_le_of_ne (not_lt.mp hn) hqb
    have hz : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
      unfold bcWeight
      rw [if_neg (not_le.mpr hlt)]
    rw [hz, zero_smul]

end general

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def topD (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) : ℝ :=
  TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c)

def NFTopForm (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re = ∫ c, topD p (D.cutF p.T.base χ F ε) w c

def NFTopPtw (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), topD p (D.cutF p.T.base χ F ε) w c = topD p F w c

def NFTopDom (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (topD p (D.cutF p.T.base χ F ε) w) volume) ∧
  ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖topD p (D.cutF p.T.base χ F ε) w c‖ ≤ h c

def NFTopId (p : KB.Pl P Wp Wq) (_χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∫ c, topD p F w c = (p.RR F 0 w [] []).re

theorem limEvT_of_NF (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hT : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopForm p χ F w)
    (hP : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopPtw p χ F w)
    (hD : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopDom p χ F w)
    (hI : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → NFTopId p χ F w) : LimEvT p χ F Y N := by
  intro w hw hl
  obtain ⟨hmeas, h, hint, hbd⟩ := hD w hw hl
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun ε c => topD p (D.cutF p.T.base χ F ε) w c) (f := topD p F w) h hmeas hbd hint
    ((hP w hw hl).mono fun c hc => Filter.Tendsto.congr' (hc.mono fun ε he => he.symm) tendsto_const_nhds)
  rw [← hI w hw hl]
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hT w hw hl ε hε).symm

end place

def NFHyp (Cb Cc : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) : Prop :=
  C6.IsCut0 χ ∧ KB.InDDplus2 P p.l0 p.T.base Cb p.Θ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A₀ m f) ∧
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ∧
    N ≤ 2 * p₀

def NFTopPtwAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopPtw p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopDomAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopDom p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

def NFTopIdAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopId p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_TopSpec
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem leibniz_class : LeibnizCls := leibnizCls_of_radLoc spectral_radial_locality

theorem density_smooth_class : DensSmoothCls := densSmoothCls_of_radLoc spectral_radial_locality

theorem thmPActualCpt_of_spec (h : RDIdentSpec) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_leaves (one_letter_density_estimate leibniz_class density_smooth_class) density_smooth_class
    (radDecay_of_spec h)

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
section
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section


section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem ttp_eq (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold Formalism.FourierDecayAlt.TBB.TTp
  rw [hz, hz']
  rfl

theorem isBoundedBilinearMap_compSh :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq' →L[ℂ] Wq) => q.1.comp q.2) :=
  { add_left := fun x₁ x₂ y => ContinuousLinearMap.add_comp x₁ x₂ y
    smul_left := fun c x y => ContinuousLinearMap.smul_comp c x y
    add_right := fun x y₁ y₂ => ContinuousLinearMap.comp_add x y₁ y₂
    smul_right := fun c x y => ContinuousLinearMap.comp_smul x c y
    bound := ⟨1, one_pos, fun x y => by simpa only [one_mul] using
      ContinuousLinearMap.opNorm_comp_le x y⟩ }


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_compSh {k r : ℕ} {f : B.Mat k r → (Wq →L[ℂ] Wp)} {A : B.Mat k r → (Wq' →L[ℂ] Wq)}
    (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (f2 g), hU1.inter hU2, ⟨hg1, hg2⟩, ?_,
    fun g hg hgv => by
      show (f g).comp (A g) = (f1 g).comp (f2 g)
      rw [he1 g hg.1 hgv, he2 g hg.2 hgv]⟩
  have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (f1 g, f2 g)) (U1 ∩ U2) := by
    first
    | exact (hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right)
    | exact (hc1.mono Set.inter_subset_left).prod (hc2.mono Set.inter_subset_right)
  exact isBoundedBilinearMap_compSh.contDiff.comp_contDiffOn hp


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_fpmSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hA : B.CkOn ⊤ (B.GV P.k P.r) A) : B.CkOn ⊤ (B.GV P.k P.r) (fpmSh q f A p₀) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat P.k P.r => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf q.T.base.z q.T.base.z').pow p₀)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc (ckOn_compSh hf hA)

end sh

def PolyOp {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (d : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∃ (n : ℕ) (c : Fin n → B.Mat k r → ℂ) (L : Fin n → (Wq' →L[ℂ] Wq)),
    (∀ i, U.IsPolyDeg d (c i)) ∧ ∀ g, A g = ∑ i, c i g • L i

def FpmShDecay : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ) (d p₀ : ℕ),
    (∀ m : ℕ, B.InCC A₀ m f) → PolyOp d A →
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m (fpmSh q f A p₀)


end

end Formalism.FourierDecayAlt.P.CutBPEq
end

