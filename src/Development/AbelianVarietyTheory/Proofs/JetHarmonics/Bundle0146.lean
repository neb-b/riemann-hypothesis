module

public import Mathlib
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EntriesOfGaps
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem liftedWord_continuousOn_GPos : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) F → ContinuousOn (p.Θ.Θ w e F) (B.GPos p.T.base) := by
  intro Wp Wq _ _ _ _ _ _ P0 p Cb w e F hDD hw hF
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hEq⟩ := hDD w hw e
  have hsub : B.GPos p.T.base ⊆ C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
  have hGPG : B.GPos p.T.base ⊆ B.GV P0.k P0.r := fun g hg => hg.1
  have hcont : ContinuousOn (B.opApply Dop F) (B.GPos p.T.base) := by
    apply Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
    intro T hT
    have h1 : ContinuousOn T.coef (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' (UU := C6.domL p.T.base ∅) (fun g hg => hg.1) (hIn.1 T hT).1).mono hsub
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF T.word T.word_lie)).mono hGPG
    exact h1.clm_apply h2
  exact hcont.congr (fun g hg => hEq F g (hsub hg))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ModelAtBare
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ModelAtPrimeToLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

end General

section Instance

variable {D : D7} {T : Top D}

theorem one_le_rank (h : LawsP T) {j : ℕ} (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.sigW]
  omega

end Instance

section Full

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

end Full

end GlobalTheory.Proof.ModelAtPrimeToLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunWeightsSum
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.RunDepth

theorem run_weights_sum : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (fR Tp hK j).n ∧ (kaR Tp hK j).n = (fR Tp hK j).n + Tp.TO * (lR Tp hK j).n ∧ WeightFamilies.dimY D j ≤ Tp.TO ∧ D.R.r ≤ (fR Tp hK j).n := by
  intro D L Pm Tp hK j hj
  have hP : (fR Tp hK j).n = Tp.nP := rfl
  have hW : (lR Tp hK j).n = Tp.nWn := rfl
  refine ⟨GlobalTheory.RunWeightTest.isF'_fWt _ _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [hP, hW, ← Tp.split]; exact kaWt_n D hK _ j
  · rw [GlobalTheory.DepthBoundTest.dimY_eq_flag hj, ← Tp.Dp_eq]
    have := Tp.TO_40
    omega
  · rw [hP, Tp.nP_eq]
    have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
    nlinarith

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoTopVectorCompactApproximantsBigCell
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem vecV_theta_approx_tendsto (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ w, KB.CutWord P p.l0 w → w.length ≤ N → ∀ (e : Wd.Ix (Fin w.length)) (q : C.LPt), Tendsto
        (fun n => D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (fun g => cut n g • D.cutF p.T.base χ f ε g)) q) atTop
        (𝓝 (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (D.cutF p.T.base χ f ε)) q)) := by
  obtain ⟨c₂, hc₂⟩ := vecV_cut_op
  refine ⟨5 * max Cb 0 + max Cb 0 ^ 2 + 1 + |c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut w hw hwN e q
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb0 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  have hcut' : ∀ n g, cut n g = 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [hcut n g]
    simp [P.JCx2.pdPsi, P.JCx2.pdPhi, P.JCx2.pdChi, P.JCx2.pdSq]
  have hFck : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF p.T.base χ f ε) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  have hFv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < ε * δ → D.cutF p.T.base χ f ε g = 0 := by
    intro g hg
    show ((χ (Gf P0.k P0.r p.T.base.z p.T.base.z' g / ε) : ℝ) : ℂ) • f g = 0
    rw [hχ0 _ (by rw [div_lt_iff₀ hε]; linarith), Complex.ofReal_zero, zero_smul]
  obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
  have hcongr : ∀ G, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e G) q =
      D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) q :=
    fun G => vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
  simp only [hcongr]
  have ho' : (o : ℝ) ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
    calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
      _ ≤ max Cb 0 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
        rw [hXn]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
          (by linarith)
      _ ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hwN) hCb0) (by linarith)
  have hκ' : (κ : ℝ) ≤ max Cb 0 * ((P0.r : ℝ) + 1) * o :=
    hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      (Nat.cast_nonneg _))
  have hthr := thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 0) c₂ o κ A hr0 hrX hN0 hCb0
    (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
  obtain ⟨bF, hbF⟩ := cutF_inCC p.T.base hχ hfA hε (A - 2 * ((P0.r : ℝ) + 1) * o) o (by linarith)
  exact hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ q _ cut nf fib o κ Dop (ε * δ)
    (A - 2 * ((P0.r : ℝ) + 1) * o) bF hfib hIn (mul_pos hε hδ) hFv hFck hbF hcut'
    (by rw [hXn]; linarith [hthr])

theorem tv_approx_tendsto : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, Tendsto (fun n : ℕ => tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w c) atTop (𝓝 (tv p (D.cutF p.T.base χ f ε) w c)) := by
  intro Cb
  obtain ⟨Cc, hC⟩ := vecV_theta_approx_tendsto Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ A N w hDD hχ hf hfA hA hw hwN ε hε c
  have h := hC Wp Wq P0 p f χ ε A N _ hDD hχ hε hf hfA hA (fun _ _ => rfl) w hw hwN
  unfold tv
  refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  apply Tendsto.const_smul
  refine (P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_
  exact ((continuous_const.clm_comp continuous_id).tendsto _).comp (h x.1 (TBB.bigPt P0.r c))

end GlobalTheory.TopVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecOpApplyCutFEq
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem vec_opApply_cutF_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Θ : B.DiffOp P.k P.r Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (δ : ℝ) (γ : C.LPt), C6.IsCut0 χ → 0 < δ → δ < TBB.Gp p γ → p.V (B.opApply Θ (D.cutF p.T.base χ f δ)) γ = p.V (B.opApply Θ f) γ := by
  intro Wp Wq _ _ _ _ _ _ P p Θ f χ δ γ hχ hδ hlt
  have hlt0 : δ < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hlt
  have hopen : IsOpen {x : B.Mat P.k P.r | δ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
  have hloc : ∀ g, δ < Gf P.k P.r p.T.base.z p.T.base.z' g →
      B.opApply Θ (D.cutF p.T.base χ f δ) g = B.opApply Θ f g := by
    intro g hg
    refine Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hopen (fun x hx => ?_) g hg
    have hx' : δ < Gf P.k P.r p.T.base.z p.T.base.z' x := hx
    simp only [D.cutF]
    rw [hχ.2.2 _ ((one_le_div hδ).mpr hx'.le), Complex.ofReal_one, one_smul]
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose h.1 h'.choose_spec.2.1
    have hlt' : δ < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hlt0
    have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h'.choose
      (D.muR p.T.base h'.choose (h.1.2 ▸ D.ptPerm γ)) (B.opApply Θ (D.cutF p.T.base χ f δ)) (B.opApply Θ f) 1 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [hloc _ (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hlt')])
    rw [e, one_smul]
  · rfl
  · rfl

end GlobalTheory.HatNF
end

