module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimTop
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

theorem limTopN_of_decay : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A b₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.CCle A 0 G b₀ → B.CkOn ⊤ (B.GV P.k P.r) G → LimTopN p nn G := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_empty
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn G A b₀ hA hG hGk γ hγ

  have hcut : ∀ (n : ℕ) (g : B.Mat P.k P.r),
      cutN P.k P.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
    rfl
  have hv := hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ G A b₀ (fun n g => cutN P.k P.r n g) hA hG hGk hcut

  have key : ∃ K : ℂ, ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), TBB.Ew p nn F (P.r + 1) [] γ =
      (K * B.hsInner (D.vecV p.T.base p.ν' p.m₀ F γ) (D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
    refine ⟨?_, fun F => ?_⟩
    swap
    unfold TBB.Ew TBB.NP KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hγ, hγ⟩, dite_eq_right (show ¬ (P.r + 1 ≤ P.r) by omega), if_pos rfl, if_pos rfl]
  obtain ⟨K, hK⟩ := key
  simp only [hK]
  have hs : Continuous (fun V : Wq →L[ℂ] Wp => B.hsVec V) := by
    unfold B.hsVec
    fun_prop
  have hcont : Continuous (fun V : Wq →L[ℂ] Wp => (K * B.hsInner V V).re) := by
    unfold B.hsInner
    exact Complex.continuous_re.comp (continuous_const.mul (hs.inner hs))
  exact (hcont.tendsto _).comp hv

theorem limTopN_cut_of_inCC : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → C6.IsCut0 χ →
    (∀ m : ℕ, B.InCC A₀ m F) → B.CkOn ⊤ (B.GV P.k P.r) F →
    ∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε) := by
  obtain ⟨c₃, hc₃⟩ := limTopN_of_decay
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn χ F A₀ hA hχ hF hFk ε hε
  obtain ⟨b₀, hb₀⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hF hε A₀ 0 (by simp)
  exact hc₃ Wp Wq P p nn (D.cutF p.T.base χ F ε) A₀ b₀ hA hb₀
    (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hFk ε)

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuity
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def RRBelowCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F →
    ∀ (i : ℕ), i ≤ P.r → ∀ (w : List C.Letter), KB.CutWord P p.l0 w → ∀ (h h' : C.LPt) (m : ℕ), 1 ≤ m →
      D.ptSize h + m = i → D.ptSize h' + m = i →
      ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
        (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nPt_app_cont (TT : ℝ) (h : C.LPt) (s : ℕ) :
    ContinuousOn (fun z : ℂ => TBB.nPt P.k P.r TT (h ++ [(s, z)])) {0}ᶜ := by
  have h1 := Formalism.FourierDecayAlt.P.LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) s h 1
  have hmap : Set.MapsTo (fun z : ℂ => ((Complex.normSq z - TT : ℝ), z)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun z hz => ⟨Set.mem_univ _, hz⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine h2.congr fun z _ => ?_
  simp only [Function.comp, TBB.nPt]
  congr 1
  simp [D.ptGG, D.ptLast]

theorem diag_cont {f : ℂ × ℂ → ℂ} (hf : ContinuousOn f (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => f (z, z)) {0}ᶜ :=
  hf.comp (Continuous.continuousOn (by fun_prop)) fun _ hz => ⟨hz, hz⟩

theorem ew_cont_of_rr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (w : List C.Letter) (h : C.LPt) (s : ℕ)
    (hRR : ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(s, cc.1)]) (h ++ [(s, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => TBB.Ew p nn F i w (h ++ [(s, z)])) {0}ᶜ := by
  have hn := nPt_app_cont (P := P) (TBB.TTp p) h s
  have hw : ContinuousOn (fun z : ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) / TBB.normC nn w : ℝ) : ℂ)) {0}ᶜ :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn hn).mul (Real.continuous_sqrt.comp_continuousOn hn)).div_const _)
  have hr := diag_cont hRR
  exact Complex.continuous_re.comp_continuousOn (hw.mul hr)

end place

theorem germContAll_of (hR : RRBelowCpt) : GermContAll := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF _ b s hb hs hbs h hh w hw _
  have hsz : D.ptSize h + s = b + s - 1 := by rw [hh.2]; omega
  refine ew_cont_of_rr p nn F (b + s - 1) w h s ?_
  rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
  · exact hR Wp Wq P p F hF (b + s - 1) (by omega) w hw.1 h h s (by omega) hsz hsz
  · have he : b + s - 1 = P.r + 1 := by omega
    rw [he] at hsz ⊢
    exact Formalism.FourierDecayAlt.P.LastBlockContinuity.rrTop_cont P p F hF Cb hCb w hw.1 h h s (by omega) hsz hsz

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LimZeroNPf
section
open Filter Topology

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

noncomputable section

theorem limZeroN_of_formLimit (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

end

end Formalism.FourierDecayAlt.P.CutBP
end

