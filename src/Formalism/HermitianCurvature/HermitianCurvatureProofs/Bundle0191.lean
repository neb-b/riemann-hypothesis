module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0158
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LocOp

def lcChi (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem lcChi_zero {x : ℝ} (hx : x < 1 / 2) : lcChi x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem lcChi_one {x : ℝ} (hx : 1 ≤ x) : lcChi x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem isCut0_lcChi : C6.IsCut0 lcChi :=
  ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
    ⟨1 / 2, by norm_num, fun _ hx => lcChi_zero hx⟩, fun _ hx => lcChi_one hx⟩

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem wR_lie {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w, B.inLie k r x.2 :=
  fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx)

theorem rw_congr_GV {F₀ : Type} [NormedAddCommGroup F₀] [NormedSpace ℂ F₀] {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → F₀} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) {w : List (B.Mat k r)}
    (hw : ∀ X ∈ w, B.inLie k r X) : ∀ g ∈ B.GV k r, g ∈ O → B.Rw w f₁ g = B.Rw w f₂ g := by
  intro g hg hgO
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR, ← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_congr_loc (wR_lie hw) hO h g hg hgO

theorem opApply_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ f₁ g = B.opApply Θ f₂ g := by
  intro g hg hgO
  unfold B.opApply
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [rw_congr_GV hO h T.word_lie g hg hgO]

theorem opAdj_congr_GV (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k r, g ∈ O → f₁ g = f₂ g) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ f₁ g = B.opAdj Θ f₂ g := by
  intro g hg hgO
  unfold B.opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  have h' : ∀ x ∈ B.GV k r, x ∈ O → T.coefAdj x (f₁ x) = T.coefAdj x (f₂ x) := fun x hx hxO => by
    rw [h x hx hxO]
  have hrev : ∀ X ∈ T.word.reverse, B.inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
  rw [rw_congr_GV hO h' hrev g hg hgO]

end gen

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem rep (hAg : LT.AgreeOm) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {Cb A₀ : ℝ} (hB : BuiltOW Cb S T f χ ν' m₀ top A₀) (v : Fin S.f) {A Bg δ : ℝ} {J : GFn S v}
    (hBg : 2 * ((S.G.r : ℝ) + 1) ≤ Bg) (hJ : LocCC S T v A Bg J) (hδ : 0 < δ) :
    ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
      (∀ g ∈ B.GV S.G.k S.G.r, Gf S.G.k S.G.r (T v).base.z (T v).base.z' g < 3 * δ / 8 → F g = 0) ∧
      ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g →
        J g = B.JF (T v).base F g := by
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  obtain ⟨F₀, hF₀c, hF₀g, hF₀e⟩ := hJ.2 (δ / 4) (by positivity)
  have hε : (0 : ℝ) < 3 * δ / 4 := by positivity
  obtain ⟨δ', -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div isCut0_lcChi hε
  obtain ⟨hFc, hFg⟩ := gcut_graded (T v).base.z (T v).base.z' (fun x => lcChi (x / (3 * δ / 4))) (δ' * (3 * δ / 4))
    hcut hBg hF₀c hF₀g
  refine ⟨D.cutF (T v).base lcChi F₀ (3 * δ / 4), hFc, hFg, ?_, ?_⟩
  · intro g _ hg
    have h1 : Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / (3 * δ / 4) < 1 / 2 := by
      rw [div_lt_iff₀ hε]; linarith
    simp [D.cutF, lcChi_zero h1]
  · intro g hg hG
    refine hAg _ _ _ _ (T v).base J _ (Set.Ioi (3 * δ / 4)) hJ.1 ?_ g hg hG
    intro q hq hGq
    have hGq' : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) := hGq
    have hx : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT := ⟨hq.1, by rw [hTT]; exact hq.2⟩
    rw [hF₀e q hx (by unfold GfP; linarith), Formalism.FourierDecayAlt.P.JCTx2.JF_cutF]
    have h1 : 1 ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) / (3 * δ / 4) := by
      rw [le_div_iff₀ hε]; linarith
    rw [lcChi_one h1]
    simp

theorem isOpen_omPlus_inter_lt {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℝ) :
    IsOpen (Q.OmPlus k r z z' ∩ {g | c < Gf k r z z' g}) :=
  (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z').inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont z z'))

end place

end LocOp

namespace LocOp

section place2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem thr_of {k r : ℕ} {o : ℕ} {A d Bg : ℝ} (hd : 0 ≤ d) (hBg : 0 ≤ Bg)
    (hA : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d + 2 * Bg * ((o : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (A - Bg * o) o := by
  have ho : (0 : ℝ) ≤ (o : ℝ) := Nat.cast_nonneg o
  have hBo : 0 ≤ Bg * (o : ℝ) := mul_nonneg hBg ho
  exact jdc_thrW o (A - Bg * o) d hd (by nlinarith)

end place2

end LocOp

theorem jALocOp_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJApply) : JALocOp := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨⟨hc, hg⟩, -⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opApply Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opApply_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  exact hTh _ _ _ _ (T v).base Θ _ F (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn _ hgO

theorem jALocAdj_of_tools (hOp : LT.OpCCg) (hAg : LT.AgreeOm) (hTh : LT.ThetaJ) : JALocAdj := by
  refine ⟨12, 2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Θ d Bg A J hd hBg hAA hCut hA hJ hFF
  have hBg0 : 0 ≤ Bg := le_trans (by positivity) hBg
  have hBo : 0 ≤ Bg * (B.opOrder Θ : ℝ) := mul_nonneg hBg0 (Nat.cast_nonneg _)
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hFc, hFg, hFz, hFe⟩ := LocOp.rep hAg hB v hBg hJ hδ
  obtain ⟨-, ⟨hc, hg⟩⟩ := hOp _ _ _ _ (T v).base Θ d Bg A (3 * δ / 8) F (by positivity) hBg0 hAA.1 hCut hFc hFg hFz
  refine ⟨B.opAdj Θ F, hc, fun m => inCC_antiA (by linarith) (hg m), fun x hx hG => ?_⟩
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgO := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hGx : 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := by
    have : δ ≤ Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) := hG
    linarith
  rw [LocOp.opAdj_congr_GV Θ (LocOp.isOpen_omPlus_inter_lt (T v).base.z (T v).base.z' (3 * δ / 4)) (f₁ := J)
    (f₂ := B.JF (T v).base F) (fun g hg hgO => hFe g ⟨hg, hgO.1⟩ hgO.2) _ hgO.1 ⟨hgO.2, hGx⟩]
  have hIn : B.InCC (A - Bg * (B.opOrder Θ : ℝ)) (B.opOrder Θ) F := hFg (B.opOrder Θ)
  set UU : Set (B.Mat S.G.k S.G.r) := {g | g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∧
    3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g} with hUU
  have hCkJ : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J := jdc_ckOn_om _ _ hJ.1.1
  have hCk : B.CkOn ⊤ UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc', he⟩ := hCkJ g₀ hg₀.1
    refine ⟨U ∩ (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
        {g | 3 * δ / 4 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g}), f',
      hU.inter (LocOp.isOpen_omPlus_inter_lt _ _ _), ⟨hgU, hg₀.1.2, hg₀.2⟩, hc'.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
    rw [← hFe g ⟨hgG, hg.2.1⟩ hg.2.2]
    exact he g hg.1 hgG
  exact (hTh _ _ _ _ (T v).base Θ _ F UU (LocOp.thr_of hd hBg0 hA) hAA.1 hAA.2 hFc hIn (fun g hg => hg.1)
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono le_top hCk)).2 _ ⟨hgO, hGx⟩

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACAsm
section
open MeasureTheory Topology Filter
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_isClosed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | Matrix.conjTranspose g * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem sgs_continuousAt_oneP {k r : ℕ} (g : B.Mat k r) :
    ContinuousAt (fun p : B.SS k r => B.sgs p g) oneP := by
  have hinv : ContinuousAt (fun A : B.Mat k r => A⁻¹) 1 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Matrix.det_one]
    exact NormedRing.inverse_continuousAt (1 : ℂˣ)
  have c11 : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r) := continuous_fst.comp continuous_fst
  have c12 : Continuous fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r) := continuous_snd.comp continuous_fst
  have c21 : Continuous fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r) := continuous_fst.comp continuous_snd
  have c22 : Continuous fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r) := continuous_snd.comp continuous_snd
  have i1 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c11.continuousAt rfl
  have i2 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c12.continuousAt rfl
  show ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * g *
    (Matrix.of p.2.2 : B.Mat k r) * (Matrix.of p.2.1 : B.Mat k r)) oneP
  exact (((i1.mul i2).mul continuousAt_const).mul c22.continuousAt).mul c21.continuousAt

theorem avgCutoff_of_parts (hB : ACBump) (hI : ACInv) (hN : ACInt) (hP : ACHaarPos) (hS : ACSmooth) :
    Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  obtain ⟨φ₀, hφ₀s, hφ₀n, hφ₀c, hφ₀O, hφ₀K⟩ := hB k r Wp Wq D K hK hKQ
  have hφ₀cont : Continuous φ₀ := hφ₀s.continuous
  set I : B.Mat k r → ℝ := fun g => ∫ p, φ₀ (B.sgs p g) ∂D.μSS with hIdef
  have hgqOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ JF.Om k r D.z D.z' := fun q hq =>
    Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q hq

  have hposI : ∀ g ∈ JF.Om k r D.z D.z', 0 < φ₀ g → 0 < I g := by
    intro g hg hφg
    have hint := hN k r Wp Wq D φ₀ hφ₀cont hφ₀c g hg
    rw [hIdef]
    refine (integral_pos_iff_support_of_nonneg (fun p => hφ₀n _) hint).2 ?_
    have hca : ContinuousAt (fun p : B.SS k r => φ₀ (B.sgs p g)) oneP :=
      hφ₀cont.continuousAt.comp (sgs_continuousAt_oneP g)
    have hev : ∀ᶠ p in 𝓝 (oneP : B.SS k r), 0 < φ₀ (B.sgs p g) := by
      refine hca.eventually (lt_mem_nhds ?_)
      show 0 < φ₀ (B.sgs oneP g)
      rw [sgs_oneP]; exact hφg
    obtain ⟨O, hOsub, hOo, hO1⟩ := mem_nhds_iff.1 hev
    exact lt_of_lt_of_le (hP k r Wp Wq D O hOo hO1)
      (measure_mono fun p hp => (ne_of_gt (hOsub hp)))

  have hcont : ContinuousOn (fun q => I (B.gq D q)) K := by
    intro q₀ hq₀
    have hq₀D := hKQ hq₀
    obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O _ (hgqOm q₀ hq₀D)
    have hgqc : ContinuousAt (fun q => B.gq D q) q₀ :=
      ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn).continuousAt
        ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D)
    have hev : (fun q => I (B.gq D q)) =ᶠ[𝓝 q₀] fun q => I' (B.gq D q) := by
      have h1 : ∀ᶠ q in 𝓝 q₀, B.gq D q ∈ U := hgqc.preimage_mem_nhds (hUo.mem_nhds hgU)
      have h2 : ∀ᶠ q in 𝓝 q₀, q ∈ JF.QDom k r D.z D.z' := (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D
      filter_upwards [h1, h2] with q hq1 hq2
      exact hII' _ hq1 (hgqOm q hq2).1
    have hI'c : ContinuousAt I' (B.gq D q₀) := (hI'U.continuousOn).continuousAt (hUo.mem_nhds hgU)
    exact ((ContinuousAt.comp_of_eq hI'c hgqc rfl).congr hev.symm).continuousWithinAt

  obtain ⟨c₀, hc₀, hc₀K⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q ∈ K, c₀ ≤ I (B.gq D q) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun q hq => by simp [hKe] at hq⟩
    · obtain ⟨q₁, hq₁, hmin⟩ := hK.exists_isMinOn hKne hcont
      exact ⟨I (B.gq D q₁), hposI _ (hgqOm q₁ (hKQ hq₁)) (hφ₀K q₁ hq₁), fun q hq => hmin hq⟩

  set s : ℝ → ℝ := fun t => Real.smoothTransition ((t - c₀ / 2) / (c₀ / 2)) with hsdef
  set σ : ℝ → ℝ := fun t => s t * t + (1 - s t) * (c₀ / 2) with hσdef
  have hc2 : 0 < c₀ / 2 := by linarith
  have hσlb : ∀ t, c₀ / 2 ≤ σ t := by
    intro t
    have h0 : 0 ≤ s t := Real.smoothTransition.nonneg _
    by_cases ht : c₀ / 2 ≤ t
    · show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      nlinarith
    · have hz : s t = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hc2.le)
      show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      rw [hz]; simp
  have hσpos : ∀ t, σ t ≠ 0 := fun t => (lt_of_lt_of_le hc2 (hσlb t)).ne'
  have hσid : ∀ t, c₀ ≤ t → σ t = t := by
    intro t ht
    have h1 : s t = 1 := Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc2]; linarith)
    show s t * t + (1 - s t) * (c₀ / 2) = t
    rw [h1]; ring
  have hσs : ContDiff ℝ ∞ σ := by
    have hs : ContDiff ℝ ∞ s :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact (hs.mul contDiff_id).add ((contDiff_const.sub hs).mul contDiff_const)

  classical
  let φ : B.Mat k r → ℂ := fun g => if g ∈ B.GV k r then ((φ₀ g * (σ (I g))⁻¹ : ℝ) : ℂ) else 0
  have hφ0 : ∀ g, g ∉ tsupport φ₀ → φ g = 0 := by
    intro g hg
    have : φ₀ g = 0 := image_eq_zero_of_notMem_tsupport hg
    simp [φ, this]
  refine ⟨φ, ?_, ⟨tsupport φ₀ ∩ B.GV k r, hφ₀c.isCompact.inter_right (gv_isClosed k r),
    fun g hg => ⟨hg.2, hφ₀O hg.1⟩, fun g hg => ?_⟩, ?_⟩
  ·
    intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O g₀ ⟨hg₀, hO⟩
      refine ⟨U, fun g => ((φ₀ g * (σ (I' g))⁻¹ : ℝ) : ℂ), hUo, hgU, ?_, ?_⟩
      · have h1 : ContDiffOn ℝ ∞ (fun g => φ₀ g * (σ (I' g))⁻¹) U :=
          hφ₀s.contDiffOn.mul ((hσs.comp_contDiffOn hI'U).inv fun g _ => hσpos _)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
      · intro g hg hgG
        show (if g ∈ B.GV k r then ((φ₀ g * (σ (∫ p, φ₀ (B.sgs p g) ∂D.μSS))⁻¹ : ℝ) : ℂ) else 0) = _
        rw [if_pos hgG, hII' g hg hgG]
    · refine ⟨(tsupport φ₀)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, fun h => hO (hφ₀O h),
        contDiffOn_const, fun g hg _ => hφ0 g hg⟩
  ·
    by_cases hgG : g ∈ B.GV k r
    · exact hφ0 g fun h => hg ⟨h, hgG⟩
    · simp [φ, hgG]
  ·
    intro p₀ hp₀ q hq
    have hgq := hgqOm q (hKQ hq)
    have hg := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D hp₀ hgq
    have hIg : I (B.sgs p₀ (B.gq D q)) = I (B.gq D q) := hI k r Wp Wq D φ₀ hφ₀cont p₀ hp₀ _
    have hIpos : 0 < I (B.gq D q) := lt_of_lt_of_le hc₀ (hc₀K q hq)
    have hae : ∀ᵐ p ∂D.μSS, φ (B.sgs p (B.sgs p₀ (B.gq D q))) =
        ((φ₀ (B.sgs p (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hG : B.sgs p (B.sgs p₀ (B.gq D q)) ∈ B.GV k r := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV D hp hg.1
      have hIp : I (B.sgs p (B.sgs p₀ (B.gq D q))) = I (B.gq D q) := by
        rw [← hIg]; exact hI k r Wp Wq D φ₀ hφ₀cont p hp _
      simp only [φ, if_pos hG, hIp, hσid _ (hc₀K q hq)]
    rw [integral_congr_ae hae, integral_complex_ofReal, integral_mul_const]
    change (((I (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) = 1
    rw [hIg, mul_inv_cancel₀ hIpos.ne', Complex.ofReal_one]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACHaarPos
section
open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

variable {k r : ℕ}

theorem haar_pos_nhds_one {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ)
    (hinv : ∀ u ∈ U, u⁻¹ ∈ U) (hunit : ∀ u ∈ U, IsUnit u.det) {V : Set (Mt k r)} (hV : IsOpen V)
    (h1 : ((1 : B.Mat k r) : Mt k r) ∈ V) : 0 < μ V := by
  rw [pos_iff_ne_zero]
  intro h0
  let W : B.Mat k r → Set (Mt k r) := fun u => lmulM u⁻¹ ⁻¹' V
  have hWo : ∀ u ∈ U, IsOpen (W u) := fun u _ => hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have hW0 : ∀ u ∈ U, μ (W u) = 0 := by
    intro u hu
    have e := h.left u⁻¹ (hinv u hu)
    have := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) u⁻¹).measurable hV.measurableSet
    rw [e] at this
    show μ (lmulM u⁻¹ ⁻¹' V) = 0
    rw [← this]; exact h0
  have hcov : (U : Set (Mt k r)) ⊆ ⋃ u ∈ U, W u := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    have e : (lmulM x⁻¹ x : Mt k r) = ((1 : B.Mat k r) : Mt k r) := by
      show x⁻¹ * x = 1
      exact Matrix.nonsing_inv_mul x (hunit x hx)
    show lmulM x⁻¹ x ∈ V
    rw [e]; exact h1
  obtain ⟨T, hTU, hTc, hTeq⟩ := TopologicalSpace.isOpen_biUnion_countable U W hWo
  have hU0 : μ (U : Set (Mt k r)) = 0 := by
    refine measure_mono_null (hcov.trans hTeq.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun u hu => hW0 u (hTU hu)
  have huniv : μ Set.univ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hU0 h.conc)
    intro x _
    by_cases hx : x ∈ (U : Set (Mt k r))
    · exact Or.inl hx
    · exact Or.inr hx
  exact h.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

theorem averaging_haar_positivity : ACHaarPos := by
  intro k r Wp Wq _ _ _ _ D O hO h1
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨A, B', hA, hB, hoA, hoB, hAB⟩ := isOpen_prod_iff.1 hO oneP.1 oneP.2 h1
  obtain ⟨V1, V2, hV1, hV2, ho1, ho2, h12⟩ := isOpen_prod_iff.1 hA oneP.1.1 oneP.1.2 hoA
  obtain ⟨V3, V4, hV3, hV4, ho3, ho4, h34⟩ := isOpen_prod_iff.1 hB oneP.2.1 oneP.2.2 hoB
  have hsub : (V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4) ⊆ O :=
    (Set.prod_mono h12 h34).trans hAB
  have uwI : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, u⁻¹ ∈ UWset k r w :=
    fun w u hu => Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hu
  have uwU : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, IsUnit u.det :=
    fun w u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have nI : ∀ u ∈ Nset k r, u⁻¹ ∈ Nset k r := fun u hu => WeylGroupFacts.mem_n_inv hu
  have nU : ∀ u ∈ Nset k r, IsUnit u.det := fun u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have p1 := haar_pos_nhds_one D.haarW (uwI _) (uwU _) hV1 ho1
  have p2 := haar_pos_nhds_one D.haarN nI nU hV2 ho2
  have p3 := haar_pos_nhds_one D.haarW' (uwI _) (uwU _) hV3 ho3
  have p4 := haar_pos_nhds_one D.haarN nI nU hV4 ho4
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  show 0 < ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) ((V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4))
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  rw [pos_iff_ne_zero] at p1 p2 p3 p4 ⊢
  exact mul_ne_zero (mul_ne_zero p1 p2) (mul_ne_zero p3 p4)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACInv
section
open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem averaging_invariance_holds : ACInv := by
  intro k r Wp Wq _ _ _ _ D φ₀ _hφ p₀ hp₀ g
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨h1, h2, h3, h4⟩ := hp₀
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun x => ((φ₀ x : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  let π1 : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun _ => 1
  have hpsi : ∀ (w : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r), psi k r w 0 y = 1 := by
    intro w y; simp [psi]
  have hJ : ∀ x : B.Mat k r, besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F x =
      ((∫ p, φ₀ (B.sgs p x) ∂D.μSS : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    intro x
    unfold besselJ
    simp only [hpsi, star_one, mul_one, one_smul, π1, F]
    rw [← integral_complex_ofReal, ← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ext
    simp [B.sgs]
  have hrep : ∀ U : Set (B.Mat k r), IsCRepOn U π1 := fun U => ⟨rfl, fun _ _ _ _ => by ext; simp [π1]⟩
  have hN := bessel_unipotent_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    (fun n₀ h => D.haarN.left n₀ h)
  have hU := bessel_unitary_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) (hrep _) (hrep _)
  have hs : B.sgs p₀ g = (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ *
      ((Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r)) * (Matrix.of p₀.2.1 : B.Mat k r) := by
    show (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ * (Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r) *
      (Matrix.of p₀.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have key : besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F (B.sgs p₀ g) =
      besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F g := by
    rw [hs, hU _ _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3, hN _ _ (WeylGroupFacts.mem_n_inv h2) _ h4]
    ext
    simp [π1, hpsi]
  rw [hJ, hJ] at key
  have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) key
  simp at this
  exact_mod_cast this

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

