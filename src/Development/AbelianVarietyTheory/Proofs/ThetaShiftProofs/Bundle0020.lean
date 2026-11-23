module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix ComplexConjugate

namespace GlobalTheory.RiemMaj

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def pc (x : Frame X.Ψ r) (v : Fin r → E) (t : X.Ψ × Fin r) : ℂ :=
  if (t.2 : ℕ) < X.p0 then hermC t.1.1 X.Gm (col (mat x t.1) t.2) (Data.emb t.1.1 v)
  else ((mat x t.1)⁻¹ *ᵥ Data.emb t.1.1 v) t.2

theorem re_xi (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
  have := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at this
  linarith

theorem norm_dmin_ortho {y : Frame X.Ψ r} (ho : X.IsOrtho y) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = 1 := by
  unfold dmin lminor
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, sgn]
  split_ifs <;> simp

theorem hermForm_diag {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) (s : X.Ψ → ℝ) (p q : X.Ψ × Fin r → ℂ) :
    hermForm (Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) (fun j => p (idx j)) (fun j => q (idx j)) =
      ∑ τ, (s τ : ℂ) * ∑ a, p (τ, a) * conj (q (τ, a)) := by
  have : hermForm (Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) (fun j => p (idx j)) (fun j => q (idx j)) =
      ∑ t : X.Ψ × Fin r, (s t.1 : ℂ) * (p t * conj (q t)) := by
    rw [hermForm, dotProduct]
    refine Fintype.sum_equiv idx _ _ fun k => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply]
    simp only [RCLike.star_def]
    ring
  rw [this, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

theorem im_diag {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {y : Frame X.Ψ r} (ho : X.IsOrtho y) (v w : Fin r → E) :
    (hermForm (Matrix.diagonal fun j => ((-2 * ((idx j).1.1 X.ξ0).im : ℝ) : ℂ)) (fun j => pc X y v (idx j))
      (fun j => pc X y w (idx j))).im = ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v w) : ℚ) : ℝ) := by
  rw [hermForm_diag X idx (fun τ => -2 * (τ.1 X.ξ0).im), UnitFrame.trace_eq_sum_re X.Ψ X.cmType, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pc]
  rw [Complex.im_ofReal_mul, UnitFrame.im_sum_periods X.p0 τ.1 X.Gm (mat y τ) (ho τ)]
  have h3 : τ.1 (herm X.Gm v w) = hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 w) := by
    simp [FD.hermC, FD.herm, FD.Data.emb, FD.cc, IsCMField.complexEmbedding_complexConj]
  rw [map_mul, map_neg, h3, Complex.mul_re, Complex.neg_re, Complex.neg_im, re_xi]
  ring

theorem maj_eq {y : Frame X.Ψ r} (hdet : ∀ τ, (mat y τ).det ≠ 0) (ho : X.IsOrtho y) (v : Fin r → E) (τ : X.Ψ) :
    (∑ a, pc X y v (τ, a) * conj (pc X y v (τ, a))).re = X.maj y τ (Data.emb τ.1 v) := by
  set u := (mat y τ)⁻¹ *ᵥ Data.emb τ.1 v with hu
  have h1 : Data.emb τ.1 v = mat y τ *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet τ)), Matrix.one_mulVec]
  conv_rhs => rw [h1]
  rw [UnipMove.GraphH.maj_ortho X ho, OrthonormalChartBounds.nsq, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  congr 1
  simp only [pc]
  split_ifs with ha
  · have hcol : col (mat y τ) a = mat y τ *ᵥ Pi.single a 1 := by
      ext k; simp [FD.col]
    rw [hcol, h1, UnitFrame.hermC_mulVec, ho τ]
    simp [Matrix.mulVec_diagonal, FD.sgn, ha]
  · rfl

theorem core {x : Frame X.Ψ r} (hx : x ∈ X.dom) {g : ℕ} (idx : Fin g ≃ X.Ψ × Fin r) {L : Type}
    (φ : L → Fin r → E) (P : L → Fin g → ℂ) (hP : ∀ a j, P a j = pc X x (φ a) (idx j))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (him : ∀ a b, (hermForm Hm (P a) (P b)).im = ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a) (φ b)) : ℚ) : ℝ)) :
    (∀ a, (hermForm Hm (P a) (P a)).re = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (φ a))) ∧
    (0 < r → X.κ0 = 2 * X.ξ0) ∧
    ∀ j, X.c (idx j).1 * (if ((idx j).2 : ℕ) < X.p0 then
      ‖dmin X.Gm x (idx j).1 (idx j).2.succ / dmin X.Gm x (idx j).1 (idx j).2.castSucc‖⁻¹
      else ‖dmin X.Gm x (idx j).1 (idx j).2.succ / dmin X.Gm x (idx j).1 (idx j).2.castSucc‖) ≤ (Hm j j).re := by
  classical
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  set b := FrameDegreeData.bOf X x
  have hy : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb
  set N := PerBor.moveMat X.p0 idx b with hN
  have hmove : ∀ a, (fun j => pc X (rmul x b) (φ a) (idx j)) = N *ᵥ P a := fun a =>
    PerBor.moveMat_mulVec X.p0 idx hb X.Gm x (φ a) _ _ (hP a) (fun _ => rfl)
  let s : X.Ψ → ℝ := fun τ => -2 * (τ.1 X.ξ0).im
  have key : Hm = Nᵀ * ((Matrix.diagonal fun j => ((s (idx j).1 : ℝ) : ℂ)) * N.map (starRingEnd ℂ)) := by
    refine UnitDet.eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [him, ← UnitDet.hermForm_mulVec, ← hmove, ← hmove]
    exact (im_diag X idx ho _ _).symm
  have hdiag : ∀ j, (Hm j j).re = ∑ k, s (idx k).1 * ‖N k j‖ ^ 2 := by
    intro j
    rw [key, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.map_apply, mul_left_comm, Complex.mul_conj,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hκ : 0 < r → X.κ0 = 2 * X.ξ0 := by
    intro hr
    refine X.κ0_xi.resolve_right fun h => ?_
    have hs : ∀ τ, s τ < 0 := fun τ => by
      have := X.κ0_sign τ
      rw [h, map_neg, map_mul, map_ofNat] at this
      simp at this
      simp only [s]
      linarith
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ⟩ : Nonempty X.Ψ := by
      by_cases h0 : τ0 ∈ X.Ψ
      · exact ⟨⟨_, h0⟩⟩
      · by_contra hn
        exact h0 ((X.cmType τ0).2 fun h' => hn ⟨⟨_, h'⟩⟩)
    let j := idx.symm (τ, ⟨0, hr⟩)
    have h1 := hpos (Pi.single j 1) (by simp)
    have h2 : hermForm Hm (Pi.single j 1) (Pi.single j 1) = Hm j j := by simp [hermForm]
    rw [h2, hdiag] at h1
    exact absurd h1 (not_lt.2 (Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonpos_of_nonneg (hs _).le (sq_nonneg _)))
  have hsc : 0 < r → ∀ τ, s τ = X.c τ := by
    intro hr τ
    have := X.κ0_sign τ
    rw [hκ hr, map_mul, map_ofNat] at this
    simp at this
    simp only [s, Data.c]
    rw [← Complex.abs_im_eq_norm.mpr (re_xi X τ.1), abs_of_neg (by linarith)]
    ring
  refine ⟨fun a => ?_, hκ, fun j => ?_⟩
  · rw [key, ← UnitDet.hermForm_mulVec, ← hmove, hermForm_diag X idx s, Complex.re_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Complex.re_ofReal_mul, maj_eq X (fun τ => (hy τ).1) ho, MajInv.maj_rmul X hx hb]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : X.maj x τ (Data.emb τ.1 (φ a)) = 0 := by
        rw [← MajInv.maj_rmul X hx hb, ← maj_eq X (fun τ => (hy τ).1) ho]
        simp
      rw [this, mul_zero, mul_zero]
    · rw [hsc hr]
  · have hr : 0 < r := (idx j).2.pos
    have hc : ∀ τ, 0 ≤ X.c τ := fun τ => by unfold Data.c; positivity
    rw [hdiag]
    simp only [hsc hr]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun k => X.c (idx k).1 * ‖N k j‖ ^ 2)
      (fun k _ => mul_nonneg (hc _) (sq_nonneg _)) (Finset.mem_univ j))
    congr 1
    have h1 := FrameDegreeData.ratio_rmul X x hx hb (idx j).1 (idx j).2
    rw [norm_div, norm_dmin_ortho X ho, norm_dmin_ortho X ho, div_one] at h1
    rw [hN, PerBor.moveMat_diag _ _ hb]
    split_ifs
    · exact (eq_inv_of_mul_eq_one_left h1.symm).symm
    · rw [norm_inv, inv_pow]
      exact eq_inv_of_mul_eq_one_right h1.symm

end Core

theorem riemann_eq_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → (∀ v, (hermForm Hm (Uw.Pm k x v) (Uw.Pm k x v)).re = ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k v : Fin r → E))) ∧ (0 < r → (U.X k).κ0 = 2 * (U.X k).ξ0) ∧ ∀ (xi : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → (lieFac Dw xi a' * (U.X k).nfac (laU U a' 0 k) x.1)⁻¹ ≤ ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k x Hm hG hU hR
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper : ∀ v s, perFr (U.X k) x.1 v (relab c σ s.1) s.2 = pc (U.X k) x.1 v (f s) := by
    intro v s
    have h := hf s
    generalize f s = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    unfold pc
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by simp)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by dsimp only; omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ s.1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  obtain ⟨h1, h2, h3⟩ := core (U.X k) x.2 (Uw.e.trans f) (fun a => (Uw.φ k a : Fin r → E)) (Uw.Pm k x)
    (fun a j => by rw [Uw.Pm_eq, hper]; rfl) (Uw.period k x).2.2.2.1 Hm hR.2.1
    (fun a b => by rw [hR.2.2, ← Uw.iso]; simp)
  refine ⟨h1, h2, fun xi a' hxi => ?_⟩
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hxi0 : 0 < xi := by
    rw [← hxi τ0]
    exact norm_pos_iff.2 ((map_ne_zero τ0).2 (U.X k).ξ0_ne)
  have hpi : 0 < 2 * Real.pi * xi := by positivity
  have e1 : (lieFac Dw xi a')⁻¹ =
      ∏ s : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (2 * Real.pi * xi) ^ ((a' (s.1, (s.2 : ℕ)) : ℝ) / 2) := by
    rw [← Real.rpow_sum_of_pos hpi, Real.rpow_def_of_pos hpi, lieFac, ← Real.exp_neg, ← Finset.sum_div,
      Fintype.sum_sigma]
    congr 1
    ring
  rw [mul_inv, e1, Data.nfac, ← Fintype.prod_prod_type', ← f.prod_comp, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Fintype.prod_sigma']
  refine Finset.prod_le_prod₀ (fun s _ => by positivity) fun s _ => ?_
  have h4 := h3 (Uw.e.symm s)
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h4
  have hinv := Function.leftInverse_invFun hbij.1 s.1
  have hc : (U.X k).c (f s).1 = 2 * xi := by rw [Data.c, hxi]
  rw [hc] at h4
  set ρ := ‖dmin (U.X k).Gm x.1 (f s).1 (f s).2.succ / dmin (U.X k).Gm x.1 (f s).1 (f s).2.castSucc‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have e2 : (ρ ^ (-(laU U a' 0 k (f s).1 (f s).2 : ℝ) / 2))⁻¹ =
      (if ((f s).2 : ℕ) < (U.X k).p0 then ρ⁻¹ else ρ) ^ ((a' (s.1, (s.2 : ℕ)) : ℝ) / 2) := by
    unfold laU
    rcases hf s with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_pos (by omega), if_neg (by omega), b, hinv, show ((f s).2 : ℕ) - (U.X k).p0 = s.2 by omega,
        neg_div, Real.rpow_neg hρ0, inv_inv]
      simp
    · have t : conjEmb (f s).1.1 = relab c σ s.1 := by
        rw [b]; exact ComplexEmbedding.involutive_conjugate E _
      rw [if_neg (by omega), if_pos (by omega), t, hinv,
        show (U.X k).p0 - 1 - ((f s).2 : ℕ) = s.2 by omega, Real.inv_rpow hρ0]
      simp
  have hρ1 : 0 ≤ (if ((f s).2 : ℕ) < (U.X k).p0 then ρ⁻¹ else ρ) := by split_ifs <;> positivity
  rw [e2, ← Real.mul_rpow hpi.le hρ1]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  have := mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
  calc _ = _ := by ring
    _ ≤ _ := this

end GlobalTheory.RiemMaj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpanFrame

open GlobalTheory.AmpleSpan

theorem secScal_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (a : ℤ)
    {T T' : Over S} (k : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (k ▷ A) (whiskerRight_snd k A) s s') :
    GeneratorPullback.SecScal L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) s' (fun _ : Fin 1 => (snd T A).left) (fun _ => a) s
      (k ▷ A).left 1 := by
  have e : (k ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  apply (secScal_const_iff hL e).2
  intro i Z r z hz
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => i) := Set.mem_iInter.2 fun _ => hz
  have le := chart_le_res A L (k ▷ A) (whiskerRight_snd k A) a (fun _ => i)
  refine Eq.symm ((congrArg (gs r z _) (H fun _ => i)).trans ?_)
  exact (gs_res r z le hm _).trans (gs_pull r (k ▷ A).left z _ (le (x := r z) hm) _)

theorem valR_of_secScal {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {ε : K → ℤ}
    {ε' : K' → ℤ} {χ : Y ⟶ X} {χ' : Y' ⟶ X} {h : Y' ⟶ Y} (e : h ≫ χ = χ')
    {s' : LB.Sec (LB.LinComb L (fun _ : K' => χ') ε')} {s : LB.Sec (LB.LinComb L (fun _ : K => χ) ε)}
    (H : GeneratorPullback.SecScal L (fun _ => χ') ε' s' (fun _ => χ) ε s h 1) {R : Type} [CommRing R] (x : Sp R ⟶ Y') (j : L.ι)
    (hx : ⊤ ≤ (x ≫ χ') ⁻¹ᵁ L.U j) :
    valR (x ≫ h) (LB.wchart L (fun _ : K => χ) (fun _ => j)) (s.f fun _ => j) =
      valR x (LB.wchart L (fun _ : K' => χ') (fun _ => j)) (s'.f fun _ => j) := by
  subst e
  have E := H (fun _ => j) (fun _ => j) (by rintro (a | a) (b | b) _ <;> rfl)
  have hm : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K' => h ≫ χ) (fun _ => j) ⊓ LB.wchart L (fun _ : K => h ≫ χ) (fun _ => j)) :=
    fun z hz => ⟨Set.mem_iInter.2 fun _ => hx hz, Set.mem_iInter.2 fun _ => hx hz⟩
  have E' := congrArg (valR x _) E
  rw [HolHom.valR_res _ _ _ hm, resTop, map_one, one_mul] at E'
  exact (HolHom.valR_comp _ _ _ _).trans (E'.trans (HolHom.valR_res _ _ _ hm))

theorem exists_span_powOver (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {N : ℕ}
    (hN : 1 ≤ N) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ (m : ℕ) (b : Fin m → LB.Sec (powOver P.A P.L U N)), ∀ (X' Y' : Scheme.{0}) [IsAffine Y']
      (h : X' ⟶ (P.A.hom ⁻¹ᵁ U).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ U.toScheme), IsPullback h f' (P.A.hom ∣_ U) g →
      ∀ (K : Type) [Fintype K] (ε : K → ℤ) (φ : X' ⟶ P.A.left), h ≫ (P.A.hom ⁻¹ᵁ U).ι = φ → ∑ k, ε k = N →
      ∀ b' : Fin m → LB.Sec (LB.LinComb P.L (fun _ : K => φ) ε),
        (∀ i, GeneratorPullback.SecScal P.L _ _ (b' i) (fun _ : Fin N => (P.A.hom ⁻¹ᵁ U).ι) (fun _ => 1) (b i) h 1) →
        ∀ s, InSpan f' b' s := by
  obtain ⟨m, b₀, hb₀⟩ := exists_sections_span_affine hS S P N hN U hU
  obtain ⟨h₀, e₀, -, -, hE⟩ := translate_powOver_LPow P.A P.isLB N (U := U) (overRes (T := baseOver S) U)
    (𝟙 U.toScheme) (by simp)
  obtain ⟨E, hE⟩ := hE (IsIso.id _)
  refine ⟨m + 1, fun i => E.symm (b₀ i), fun X' Y' _ h f' g sq K _ ε φ e hε b' hb' s => ?_⟩
  let T' : Over S := Over.mk (g ≫ U.ι)
  have : IsAffine T'.left := ‹IsAffine Y'›
  let k : T' ⟶ overRes (T := baseOver S) U := Over.homMk g (by simp [T'])
  obtain ⟨h', e', sq', -, -⟩ := translate_powOver_LPow P.A P.isLB N (U := U) T' g rfl
  let b'' : Fin (m + 1) → LB.Sec (LPow P.A P.L N T') := fun i =>
    SecM.toSec P.A (SecAff.pull P.A P.L N k (SecM.ofSec P.A (b₀ i)))
  have hb'' : ∀ i, IsPullSec P.A P.L N (k ▷ P.A) (whiskerRight_snd k P.A) (b₀ i) (b'' i) := fun i =>
    (SecAff.isPullSec_iff P.A P.L N _ _ _).2 rfl
  have hsp := hb₀ T' k b'' hb''
  let θ := sq.isoIsPullback _ _ sq'
  have θ₁ : θ.hom ≫ h' = h := sq.isoIsPullback_hom_fst _ _ sq'
  have θ₂ : θ.hom ≫ (fst T' P.A).left = f' := sq.isoIsPullback_hom_snd _ _ sq'
  have θ₃ : θ.hom ≫ (snd T' P.A).left = φ := by rw [← e', ← Category.assoc, θ₁, e]
  obtain ⟨F, hF⟩ := exists_equiv_secScal P.isLB (h := θ.hom) (formEq_const (K := Fin 1) (K' := K)
    (ε := fun _ => (N : ℤ)) (ε' := ε) θ₃ (by simp [hε]))
  have θ₄ : θ.hom ≫ (k ▷ P.A).left ≫ h₀ = h := by
    rw [← cancel_mono (P.A.hom ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, e₀, ← Over.comp_left, whiskerRight_snd, θ₃, e]
  refine InSpan.secScal P.isLB (h := θ.hom) (f := (fst T' P.A).left) (g := 𝟙 Y') (θ₂.trans (Category.comp_id _).symm)
    (t := b'') (s := F.symm s) ((inSpan_iff_mem_span P.A b'' _).2 (by rw [hsp]; trivial)) (fun i => ?_)
    ((hF _ _).2 (F.apply_symm_apply s))
  apply (secScal_iff_sval P.isLB).2
  intro Z r z J hJ
  rw [← SectionScalarValuation.secScal_sval (hb' i) r z hJ, ← SectionScalarValuation.secScal_sval (secScal_of_isPullSec P.A P.isLB N k (hb'' i)) _ z hJ,
    ← SectionScalarValuation.secScal_sval ((hE _ _).2 (E.apply_symm_apply (b₀ i))) _ z hJ, Category.assoc, Category.assoc, θ₄]

end GlobalTheory.SpanFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

section Val

variable {A : Type} [CommRing A] {X Y : Scheme.{0}}

variable {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}

theorem valR_of_corr (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (e : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (h : LB.Gen.Corr L φ ε φ' ε t t')
    (x : Sp A ⟶ Y) (j : K → L.ι) :
    valR x (LB.wchart L φ j) (t.s j).val = valR x (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  rw [TorusCoord.gen_eq_of_corr hL ht ht' h]

theorem top_le_wchart_iff {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    ⊤ ≤ LB.wchart L (fun k => h ≫ φ k) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j :=
  ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
    fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩

theorem valR_pullGen (φ : K → (Y ⟶ X)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Sp A ⟶ Y) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j).val =
      valR h (LB.wchart L φ j) (t.s j).val := by
  by_cases H : ⊤ ≤ h ⁻¹ᵁ LB.wchart L φ j
  · have H' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := (top_le_wchart_iff φ h j).2 H
    refine (HolHom.valR_res (𝟙 (Sp A)) _ _ H').trans ?_
    exact (HolHom.valR_comp (𝟙 (Sp A)) h _ _).symm.trans (by rw [Category.id_comp]; rfl)
  · have H' : ¬ ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j := fun H' => H ((top_le_wchart_iff φ h j).1 H')
    exact (dif_neg H').trans (Eq.symm (show valR h (LB.wchart L φ j) (t.s j).val = 0 from dif_neg H))

end Val

section Pull

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

theorem gtφT_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) :
    Out.DegPre.gtφT D T' b' χ = fun k => h ≫ Out.DegPre.gtφT D T b χ k := by
  funext k
  rw [TorusCoord.gtφT_eq, ← Category.id_comp (D.Oφ b' χ k)]
  exact ((TorusCoord.comp_eq_of_left b b' h (𝟙 _) (by rw [Category.id_comp, e])).1 χ k).symm

theorem top_le_wchart_pull {T T' : Over (Sp R)} {b : T ⟶ D.P.A} {b' : T' ⟶ D.P.A} {h : T'.left ⟶ T.left}
    (e : b'.left = h ≫ b.left) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D T' b' χ) j ↔ ⊤ ≤ h ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D T b χ) j := by
  rw [gtφT_pull e, top_le_wchart_iff]

theorem valR_of_isPull {A : Type} [CommRing A] {p : Sp A ⟶ Sp R} {T : Over (Sp R)} {g : Out.GtPt D T}
    {g' : Out.GtPt D (Over.mk p)} {h : Sp A ⟶ T.left} (H : Out.GtPt.IsPull (T' := Over.mk p) h g g') (χ : D.X)
    (j : Fin 4 → D.P.L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart D.P.L (Out.DegPre.gtφT D (Over.mk p) g'.b χ) j) ((g'.s χ).s j).val =
      valR h (LB.wchart D.P.L (Out.DegPre.gtφT D T g.b χ) j) ((g.s χ).s j).val :=
  (valR_of_corr D.P.isLB (gtφT_pull H.1 χ) (g'.isGen χ) (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) (H.2 χ) _ j).trans
    (valR_pullGen _ _ h j)

end Pull

section Ex

variable [Algebra (FractionRing ℂ) ℂ] {D : Out.DegPre ℂ} {g : ℕ} {ex : (Fin g → ℂ) → Out.GtPtF D ℂ}

theorem b_add (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (z z' : Fin g → ℂ) :
    (ex (z + z')).b = (ex z).b * (ex z').b := (h z z').1

theorem b_zero (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) : (ex 0).b = 1 := by
  have := b_add h 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem b_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) (n : ℕ) (z : Fin g → ℂ) :
    (ex ((n : ℂ) • z)).b = (ex z).b ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, b_zero h]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, b_add h, ih, pow_succ]

theorem top_le_wchart_nsmul (h : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) {n : ℕ} {b₀ : D.P.A ⟶ D.P.A}
    (hb : b₀ = 𝟙 D.P.A ^ n) (z : Fin g → ℂ) (χ : D.X) (j : Fin 4 → D.P.L.ι) :
    ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b χ) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A b₀ χ) j :=
  top_le_wchart_pull (T' := Out.TF (R := ℂ) ℂ) (h := (ex z).b.left) (by
    rw [b_nsmul h, hb, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]) χ j

theorem tf_hom [IsScalarTower ℂ (FractionRing ℂ) ℂ] : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact Spec.map_id _

def IsRatio (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (n : ℕ) (s₀ : Out.GtPt D D.P.A) (u : D.X → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ x z j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j →
    chiVal (ex ((n : ℂ) • z)) x j = u x z * valAt' (show Sp ℂ ⟶ _ from (ex z).b.left)
      (LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A s₀.b x) j) ((s₀.s x).s j).val

end Ex

end GlobalTheory.AbelianLetters
end
end

