module

public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0175
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0161
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEllRegBridge
section
namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open MeasureTheory
open scoped ContDiff

def EllRegBridge : Prop := ZetaZeros.D.EllReg.Internal → EllRegW

section bridge

variable {d : ℕ}

noncomputable abbrev brT (d : ℕ) : ZetaZeros.D.EllReg.E d ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ

lemma brT_ev (j : Fin d) : brT d (ZetaZeros.D.EllReg.ev j) = Pi.single j 1 := by
  unfold ZetaZeros.D.EllReg.ev
  rfl

lemma dw_comp_brT (w : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    ZetaZeros.D.EllReg.dw w (f ∘ brT d) = pdc w f ∘ brT d := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (ZetaZeros.D.EllReg.dw w (f ∘ brT d)) x (ZetaZeros.D.EllReg.ev j) =
      fderiv ℝ (pdc w f) (brT d x) (Pi.single j 1)
    rw [ih, (brT d).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, brT_ev]

noncomputable def brSys {ι : Type} (P : ι → SOp d) : ZetaZeros.D.EllReg.Sys d ι where
  ord i := (P i).ord
  a i n w := if h : n < (P i).ord + 1 then (P i).a ⟨n, h⟩ w ∘ brT d else 0

lemma brSys_tr {ι : Type} (P : ι → SOp d) (i : ι) (φ : (Fin d → ℝ) → ℂ) (x : ZetaZeros.D.EllReg.E d) :
    (brSys P).tr i (φ ∘ brT d) x = (P i).tr φ (brT d x) := by
  unfold ZetaZeros.D.EllReg.Sys.tr ZetaZeros.D.EllReg.trOp SOp.tr
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
  congr 1
  have e : (fun y => (brSys P).a i k w y * (φ ∘ brT d) y) =
      (fun y' => (P i).a k w y' * φ y') ∘ brT d := by
    funext y
    simp only [brSys, Function.comp_apply]
    rw [dif_pos (show (k : ℕ) < (P i).ord + 1 from k.isLt)]
    rfl
  rw [e, dw_comp_brT]
  rfl

lemma brSys_symb {ι : Type} (P : ι → SOp d) (i : ι) (x ξ : ZetaZeros.D.EllReg.E d) :
    (brSys P).symb i x ξ = (P i).symb (brT d x) (brT d ξ) := by
  unfold ZetaZeros.D.EllReg.Sys.symb SOp.symb
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [brSys, dif_pos (Nat.lt_succ_self _)]
  rw [mul_comm]
  rfl

end bridge

theorem elliptic_regularity_transfer_holds : EllRegBridge := by
  intro hI d ι _ P U u hU ha hu hweak hsymb
  have hHyp : ZetaZeros.D.EllReg.Hyp (brSys P) (brT d ⁻¹' U) (u ∘ brT d) := by
    refine ⟨hU.preimage (brT d).continuous, ?_, ?_, hu.comp (brT d).continuous.continuousOn (fun x hx => hx), ?_⟩
    · intro i n w
      simp only [brSys]
      split_ifs with h
      · exact (ha i ⟨n, h⟩ w).comp_continuousLinearMap ((brT d : ZetaZeros.D.EllReg.E d →L[ℝ] (Fin d → ℝ)))
      · exact contDiffOn_const
    · intro x hx ξ hξ
      have hξ' : brT d ξ ≠ 0 := fun h => hξ ((brT d).injective (h.trans (map_zero (brT d)).symm))
      obtain ⟨i, hi⟩ := hsymb (brT d x) hx (brT d ξ) hξ'
      exact ⟨i, by rw [brSys_symb]; exact hi⟩
    · intro i φ hφ hφc hφU
      have hψ : ContDiff ℝ ∞ (φ ∘ (brT d).symm) := hφ.comp (brT d).symm.contDiff
      have hψc : HasCompactSupport (φ ∘ (brT d).symm) := hφc.comp_homeomorph (brT d).symm.toHomeomorph
      have hψU : tsupport (φ ∘ (brT d).symm) ⊆ U := by
        intro y hy
        have hy' : y ∈ tsupport (φ ∘ (brT d).symm.toHomeomorph) := hy
        rw [tsupport_comp_eq_preimage φ (brT d).symm.toHomeomorph] at hy'
        have h1 := hφU hy'
        have h2 : brT d ((brT d).symm y) ∈ U := h1
        rwa [ContinuousLinearEquiv.apply_symm_apply] at h2
      have hφeq : φ = (φ ∘ (brT d).symm) ∘ brT d := by
        funext x
        simp
      have h1 := hweak i (φ ∘ (brT d).symm) hψ hψc hψU
      rw [hφeq]
      simp_rw [brSys_tr]
      rw [← h1]
      exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
        (fun y => u y * (P i).tr (φ ∘ (brT d).symm) y)
  have key := hI d ι (brSys P) (brT d ⁻¹' U) (u ∘ brT d) hHyp
  have h2 := key.comp_continuousLinearMap (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d))
  have e1 : (u ∘ brT d) ∘ (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) = u := by
    funext x
    show u (brT d ((brT d).symm x)) = u x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have e2 : (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) ⁻¹' (brT d ⁻¹' U) = U := by
    ext x
    show brT d ((brT d).symm x) ∈ U ↔ x ∈ U
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [e1, e2] at h2
  exact h2

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

def JALocOp : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)

def JALocAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)

def JALocPhi : Prop :=
  ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)

def JALocAdd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')

def LocalSquareIntegrableTransfer : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

theorem nDim_nonneg (k r : ℕ) : 0 ≤ nDim k r := by unfold nDim; positivity

theorem mul_mul_le_mul_mul_of_nonneg {a b x y : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) : a * x * y ≤ b * x * y :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hx) hy

theorem mul_le_of_le_of_mul_le {a b x B : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hB : b * x ≤ B) : a * x ≤ B :=
  (mul_le_mul_of_nonneg_right h hx).trans hB

theorem jALocCC_of_leaves (h2 : JALocOp) (h3 : JALocAdj) (h4 : JALocPhi) (h5 : JALocAdd) (h8 : LocalSquareIntegrableTransfer) :
    JALocCC := by
  obtain ⟨C2, G2, -, H2⟩ := h2
  obtain ⟨C3, G3, -, H3⟩ := h3
  obtain ⟨G4, -, H4⟩ := h4
  obtain ⟨C5, H5⟩ := h5
  obtain ⟨C8, H8⟩ := h8
  refine ⟨max (max C2 C3) (max C5 C8), max (max G2 G3) (max G4 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  have hn := nDim_nonneg S.G.k S.G.r
  have hn2 : 0 ≤ nDim S.G.k S.G.r ^ 2 := by positivity
  have hr2 : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 2 := by positivity
  have c2 : C2 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_left _ _)
  have c3 : C3 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_right _ _)
  have c5 : C5 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_left _ _)
  have c8 : C8 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_right _ _)
  have g2 : G2 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_left _ _)
  have g3 : G3 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_right _ _)
  have g4 : G4 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_right (le_max_left _ _)
  refine ⟨fun F A Bg h1 h2 h3 h4 => locCC_JF h1 h2 h3 h4, ?_, ?_, ?_, ?_, fun Bg A c J hJ => locCC_smul c hJ,
    fun Bg A A' J h hJ => locCC_antiA h hJ, ?_⟩
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H2 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g2 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c2 hr hn2]) hA) hJ hFF
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H3 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g3 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c3 hr hn2]) hA) hJ hFF
  · intro φ Bg A J hφ hld hG hJ hFF
    exact H4 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v φ Bg A J hφ hld (mul_le_of_le_of_mul_le g4 hr hG) hJ hFF
  · intro Bg A J J' hBg hA hJ hJ'
    exact H5 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A J J' hBg (le_trans (mul_mul_le_mul_mul_of_nonneg c5 hr hn2) hA) hJ hJ'
  · intro Bg A ε J e hFr hBg hε hA hJ π
    exact H8 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A ε J e hFr hBg hε
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c8 hr2 hn]) hA) hJ π

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
section
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ACProper : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (C C' : Set (B.Mat k r)),
    IsCompact C → IsCompact C' → C' ⊆ JF.Om k r D.z D.z' →
    ∃ P : Set (B.SS k r), IsCompact P ∧ ∀ p, D.inSS p → ∀ g ∈ C', B.sgs p g ∈ C → p ∈ P

def ACBump : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ JF.QDom k r D.z D.z' →
    ∃ φ₀ : B.Mat k r → ℝ, ContDiff ℝ ∞ φ₀ ∧ (∀ g, 0 ≤ φ₀ g) ∧ HasCompactSupport φ₀ ∧
      tsupport φ₀ ⊆ Q.OmPlus k r D.z D.z' ∧ ∀ q ∈ K, 0 < φ₀ (B.gq D q)

def ACInv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ), Continuous φ₀ →
    ∀ p₀, D.inSS p₀ → ∀ g : B.Mat k r, ∫ p, φ₀ (B.sgs p (B.sgs p₀ g)) ∂D.μSS = ∫ p, φ₀ (B.sgs p g) ∂D.μSS

def ACInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ), Continuous φ₀ → HasCompactSupport φ₀ →
    ∀ g ∈ JF.Om k r D.z D.z', Integrable (fun p => φ₀ (B.sgs p g)) D.μSS

def ACHaarPos : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (O : Set (B.SS k r)), IsOpen O → oneP ∈ O → 0 < D.μSS O

def ACSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ),
    ContDiff ℝ ∞ φ₀ → HasCompactSupport φ₀ → tsupport φ₀ ⊆ Q.OmPlus k r D.z D.z' →
    ∀ g₀ ∈ JF.Om k r D.z D.z', ∃ (U : Set (B.Mat k r)) (I' : B.Mat k r → ℝ), IsOpen U ∧ g₀ ∈ U ∧
      ContDiffOn ℝ ∞ I' U ∧ ∀ g ∈ U, g ∈ B.GV k r → ∫ p, φ₀ (B.sgs p g) ∂D.μSS = I' g

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLAsm
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem sAPairOne_of_parts (hZ : SAZero) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) :
    SAPairOne := by
  obtain ⟨C1, hZ'⟩ := hZ
  obtain ⟨C2, hL'⟩ := hL
  obtain ⟨C3, hE'⟩ := hE
  obtain ⟨C4, hJC'⟩ := hJC
  obtain ⟨C5, hB3'⟩ := hB3
  refine ⟨max C1 (max C2 (max C3 (max C4 C5))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θ hΘ K hK J hJ hΘK hΘJ hKt
  have mono : ∀ c : ℝ, c ≤ max C1 (max C2 (max C3 (max C4 C5))) → BuiltOW c S T f χ ν' m₀ top A₀ :=
    fun c h => ⟨isBuiltPlace_mono h hB.1, hB.2⟩
  have hB1 := mono C1 (le_max_left _ _)
  have hB2 := mono C2 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hB3 := mono C3 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hB4 := mono C4 (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hB5 := mono C5 (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs

  set Cs : Set (MA.E (D.parOf S v).r) :=
    ⋃ π, tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
      MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) with hCsdef
  have hCc : IsCompact Cs := isCompact_iUnion fun π => (hKt π).1
  have hCQ : Cs ⊆ Qs := Set.iUnion_subset fun π => (hKt π).2
  have hCcl : IsClosed Cs := hCc.isClosed
  have hK0 : ∀ y ∈ Qs, y ∉ Cs → K (B.gq (T v).base y) = 0 := by
    intro y hy hyC
    refine hZ' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he K hK y hy fun π => ?_
    have hn : y ∉ tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) := fun h => hyC (Set.mem_iUnion.2 ⟨π, h⟩)
    have h0 := image_eq_zero_of_notMem_tsupport hn
    simp only [MA.ext] at h0
    first
    | exact h0 hy
    | exact (dif_pos hy).symm.trans h0
  have hΘK0 : ∀ y ∈ Qs, y ∉ Cs → B.opApply Θ K (B.gq (T v).base y) = 0 := fun y hy hyC =>
    hL' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v Θ hΘ K hK (Qs \ Cs) ((MA.Qset_open _ _).sdiff hCcl)
      Set.sdiff_subset (fun y' hy' => hK0 y' hy'.1 hy'.2) y ⟨hy, hyC⟩
  refine ⟨fun π => ?_, ?_⟩
  ·
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he (B.opApply Θ K) hΘK π
    have hsupp : Function.support (MA.ext ((trJ S T v e (B.opApply Θ K) π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) ⊆ Cs := by
      intro y hy
      by_contra hyC
      apply hy
      by_cases hyQ : y ∈ Qs
      · simp only [MA.ext]
        unfold trJ
        rw [En.toSm_val_of_mem _ hsm]
        simp [hΘK0 y hyQ hyC, GA.hsVec_zero']
      · simp only [MA.ext]
        first
        | exact fun h => absurd h hyQ
        | exact dif_neg hyQ
    have hts := closure_minimal hsupp hCcl
    exact ⟨hCc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hCQ⟩
  ·
    obtain ⟨F₁, U₁, -, hCU₁, hF₁s, hF₁c, hF₁O, hF₁e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v K hK Cs hCc hCQ
    obtain ⟨F₂, U₂, hU₂o, hCU₂, hF₂s, hF₂c, hF₂O, hF₂e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v J hJ Cs hCc hCQ
    have hKF₁ : ∀ y ∈ Qs, K (B.gq (T v).base y) = B.JF (T v).base F₁ (B.gq (T v).base y) := by
      intro y hy
      by_cases hyU : y ∈ U₁
      · exact ((hF₁e y hy).1 hyU).symm
      · have hyC : y ∉ Cs := fun h => hyU (hCU₁ h)
        rw [hK0 y hy hyC, (hF₁e y hy).2 (hK0 y hy hyC)]
    have hc1 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₁ hF₁s hF₁c hF₁O Set.univ K isOpen_univ hK
      (fun y hy _ => hKF₁ y hy)
    have hc2 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₂ hF₂s hF₂c hF₂O U₂ J hU₂o hJ
      (fun y hy hyU => ((hF₂e y hy).1 hyU).symm)
    obtain ⟨hF₁5, hF₂5, hΘF₁5, hΘF₂5, hβ⟩ :=
      hB3' E Wp Wq S T f χ ν' m₀ top A₀ hB5 v Θ hΘ F₁ F₂ hF₁s hF₁c hF₁O hF₂s hF₂c hF₂O
    have hLp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he (B.opApply Θ K) J (B.opApply Θ F₁) F₂
      hΘK hJ hΘF₁5 hF₂5 (Filter.Eventually.of_forall fun y hy => ⟨(hc1 y hy trivial).1, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hΘK0 y hy hyC)
        exact ((hF₂e y hy).1 (hCU₂ hyC)).symm⟩)
    have hRp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he K (B.opAdj Θ J) F₁ (B.opAdj Θ F₂)
      hK hΘJ hF₁5 hΘF₂5 (Filter.Eventually.of_forall fun y hy => ⟨hKF₁ y hy, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hK0 y hy hyC)
        exact (hc2 y hy (hCU₂ hyC)).2⟩)
    rw [hLp, hRp]
    exact hβ

theorem sAPairL_of_parts (hF : JAFFStable) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) : SAPairL :=
  sAPairL_of_one hF (sAPairOne_of_parts self_adjoint_zero_holds hL hE hJC hB3)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQHatQQ
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

theorem jDHatOpQQ_of_opA_opR_residue_splitting (hA : JDOpA) (hR : JDOpR) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : JDHatOpQQ := by
  obtain ⟨KA, hKA, hA⟩ := hA
  obtain ⟨KR, hKR, hR⟩ := hR
  refine ⟨max KA KR, le_max_of_le_left hKA, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hGQ hML X hX
  have hAat := hA (max KA KR) (le_max_left _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hML
  have hRat := hR (max KA KR) (le_max_right _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGQ hML
  have hAh : ∀ y, HReal (max KA KR) S T v e L (L.Ahat y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hAat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hAhv : ∀ y, HReal (max KA KR) S T v e L (L.Ahatv y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hAat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hRh : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hRat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hRhv : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhvM (D.parOf S v) L y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hRat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hx : ∀ y, xInvM (D.parOf S v) y ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) :=
    fun y => jdh_kap_mem _ L _
  obtain ⟨ν, hνi, hνr⟩ := h4 (D.parOf S v)
  have hR0n : ∀ j, HReal (max KA KR) S T v e L (L.R0 (ν j)) := fun j => by
    rw [h1 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRh _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_SSn_mem _ L l hl))
      (jdh_kap_mem _ L _)) (hAh _)
  have hR0vn : ∀ j, HReal (max KA KR) S T v e L (L.R0v (ν j)) := fun j => by
    rw [h2 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRhv _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_kap_mem _ L _))
      (jdh_SSns_mem _ L l hl)) (hAhv _)
  have key : HReal (max KA KR) S T v e L X := by
    simp only [MA.hatSet, Set.mem_union, Set.mem_range] at hX
    rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
    · exact hAh y
    · rw [(h3 _ L ν hνi y).1]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0n j)
    · exact hAhv y
    · rw [(h3 _ L ν hνi y).2]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0vn j)
  exact key

end

end Formalism.FourierDecayAlt.P.CutMP
end

