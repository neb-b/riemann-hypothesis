module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0259
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0252
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JslHsInnerSelfNorm
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section JSL

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

private theorem opL_eq_zero_of_eventuallyEq_zero {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m)
    (j : Fin 6) (f : (Fin m → ℂ) → E) (x : Fin m → ℂ) (h : f =ᶠ[𝓝 x] 0) : opL l j f x = 0 := by
  have h0 : f x = 0 := h.eq_of_nhds
  have hd : fderiv ℝ f x = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply (0 : E)
  fin_cases j
  · show pOp l f x = 0
    unfold pOp QuantumDeterminants.wirt
    rw [hd]
    simp
  · show cOp l f x = 0
    simp [cOp, h0]
  · show ciOp l f x = 0
    simp [ciOp, h0]
  · show pbOp l f x = 0
    unfold pbOp QuantumDeterminants.wirtBar
    rw [hd]
    simp
  · show cbOp l f x = 0
    simp [cbOp, h0]
  · show cbiOp l f x = 0
    simp [cbiOp, h0]

theorem jsl_wOp_lc (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) :
    ∀ Φ ∈ lcSub k r z z' π π', wOp X l js Φ ∈ lcSub k r z z' π π' := by
  have hmem : ∀ Ψ : RadSp k r z z' π π', Ψ ∈ lcSub k r z z' π π' ↔ ∀ c ∈ OmX r, LCptAt Ψ c :=
    fun Ψ => Iff.rfl
  have hop : ∀ j, ∀ Ψ ∈ lcSub k r z z' π π', X.op l j Ψ ∈ lcSub k r z z' π π' := by
    intro j Ψ hΨ
    rw [hmem] at hΨ ⊢
    intro c hc
    obtain ⟨U', hU', hcU, K, hK, hKG, h0⟩ := hΨ c hc
    refine ⟨U', hU', hcU, K, hK, hKG, fun c' hc' g hg hgK => ?_⟩
    rw [X.op_apply]
    show opL l j (fun c'' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c'' g) c' = 0
    apply opL_eq_zero_of_eventuallyEq_zero
    filter_upwards [hU'.mem_nhds hc'] with c'' hc''
    exact h0 c'' hc'' g hg hgK
  induction js with
  | nil =>
    intro Φ hΦ
    simpa [wOp] using hΦ
  | cons j js ih =>
    intro Φ hΦ
    show X.op l j (wOp X l js Φ) ∈ lcSub k r z z' π π'
    exact hop j _ (ih Φ hΦ)

theorem jsl_hsInner_self_norm (C : Wq →L[ℂ] Wp) : ‖B.hsInner C C‖ = ‖B.hsVec C‖ ^ 2 := by
  rw [B.hsInner, inner_self_eq_norm_sq_to_K]
  simp [norm_pow]

theorem jsl_hs_comb_le {K : ℕ} (a : Fin K → ℂ) (A : Fin K → (Wq →L[ℂ] Wp)) :
    ‖B.hsInner (∑ i, a i • A i) (∑ i, a i • A i)‖ ≤ (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsInner (A i) (A i)‖ := by
  have hlin : B.hsVec (∑ i, a i • A i) = ∑ i, a i • B.hsVec (A i) := by
    change hsVecLin (∑ i, a i • A i) = ∑ i, a i • hsVecLin (A i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  rw [jsl_hsInner_self_norm, hlin]
  simp_rw [jsl_hsInner_self_norm]
  calc ‖∑ i, a i • B.hsVec (A i)‖ ^ 2 ≤ (∑ i, ‖a i • B.hsVec (A i)‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (K : ℝ) * ∑ i, ‖a i • B.hsVec (A i)‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i • B.hsVec (A i)‖)
    _ = (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsVec (A i)‖ ^ 2 := by
        simp [norm_smul, mul_pow]

theorem jsl_pairAt_comb_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {K : ℕ}
    (a : Fin K → ℂ) (u : RadSp k r z z' π π') (v : Fin K → RadSp k r z z' π π')
    (hv : ∀ i, v i ∈ lcSub k r z z' π π') (x : Fin r → ℂ)
    (hx : ∀ g, (u : Fn k r (Wq →L[ℂ] Wp)) x g = ∑ i, a i • (v i : Fn k r (Wq →L[ℂ] Wp)) x g) :
    ‖pairAt μ u u x‖ ≤ (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖pairAt μ (v i) (v i) x‖ := by
  have hint : ∀ i, Integrable (fun g : Mt k r => ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
      ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖) μ := fun i => (int_lc μ hμ (hv i) (hv i) x).norm
  rw [norm_pairAt_selfI]
  simp only [norm_pairAt_selfI]
  calc ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
        ((u : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖ ∂μ
      ≤ ∫ g : Mt k r, (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
        ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖ ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((integrable_finsetSum _ fun i _ => (hint i).const_mul _).const_mul _) (ae_of_all _ fun g => ?_)
        dsimp only
        rw [hx]; exact jsl_hs_comb_le _ _
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp only [integral_const_mul]

private theorem integral_norm_ofReal_eq_norm_integral_of_nonneg {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∫ a, ‖((f a : ℝ) : ℂ)‖ ∂ν = ‖∫ a, ((f a : ℝ) : ℂ) ∂ν‖ := by
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (hf _)]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hf)]

theorem jsl_int_norm_self (μ : Measure (Mt k r)) (i : Fin (r + 1)) (v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ∫ c' : Cf r i, ‖wtI i c' * pairAt μ v v (glue i c c')‖ =
      ‖∫ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c')‖ := by
  have key : ∀ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c') =
      (((∏ l, ‖c' l‖ ^ (-2 : ℤ)) *
        ∫ g : Mt k r, ‖B.hsVec ((v : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro c'
    have hh : ∀ A : Wq →L[ℂ] Wp, B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := fun A => by
      rw [B.hsInner, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [wtI, pairAt]
    simp_rw [hh]
    rw [integral_complex_ofReal, Complex.ofReal_mul]
  simp_rw [key]
  apply integral_norm_ofReal_eq_norm_integral_of_nonneg
  intro c'
  apply mul_nonneg
  · exact Finset.prod_nonneg fun l _ => by positivity
  · exact integral_nonneg fun g => by positivity

theorem jsl_glue_self (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  unfold glue
  rw [dite_eq_right (by simp [Fin.val_succ])]
  simp

end JSL

theorem jSL2Loc_of : JSWordNF → JSRadLoc → SpectralL2Locality := by
  intro hNF hRad Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ js t0 ht0
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ
  obtain ⟨hΨlc, s, ε, G, hε, hN, hG, hΨv⟩ := hΨ

  let Wv : Module.End ℂ (RadSp P.k P.r z z' π π') :=
    P5.mulOp (fun x => fsv s (x.1 l)) (P5.contDiff_fsv_coord l s) (fun _ _ _ _ _ _ => rfl)
  have hW : multiplicationOperator Wv (fun c _ => fsv s (c l)) := P5.mulOp_isMulOp _ _ _
  let Wn : Module.End ℂ (RadSp P.k P.r z z' π π') :=
    P5.mulOp (fun x => fsv (-s) (x.1 l)) (P5.contDiff_fsv_coord l (-s)) (fun _ _ _ _ _ _ => rfl)
  have hWn : multiplicationOperator Wn (fun c _ => fsv (-s) (c l)) := P5.mulOp_isMulOp _ _ _
  have hΦlc : Wn Ψ ∈ lcSub P.k P.r z z' π π' := mul_lc hWn Ψ hΨlc
  have hΦv : ∀ y ∈ DomR P.k P.r z z', ((Wn Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
    intro y hy
    rw [hWn Ψ y.1 y.2, hΨv y hy, smul_smul, fsv_neg_mul_fsv, one_smul]
  have hΨeq : Wv (Wn Ψ) = Ψ := by
    apply Subtype.ext
    funext c' g
    show ((Wv (Wn Ψ) : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g
    rw [hW (Wn Ψ) c' g, hWn Ψ c' g, smul_smul, fsv_mul_fsv_neg, one_smul]

  obtain ⟨K, m, ab, hm, hab, hE⟩ := hNF P.k P.r z z' Wp Wq π π' X l s Wv hW js
  have hR : ∀ i, ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
      LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧
        ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M := fun i =>
    hRad Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl ε hε G hN hG (Wn Ψ) hΦlc hΦv c hc (ab i)
      (hab i) t0 ht0
  choose ε' hε' M hM using hR
  have hac : ∀ i, ContinuousAt (fun t => m i t * fsv s t) t0 := fun i =>
    ((hm i).continuousAt (isOpen_compl_singleton.mem_nhds ht0)).mul
      (P5.contDiff_fsv s).continuous.continuousAt
  have hev : ∀ᶠ t in 𝓝 t0, ∀ i, (LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧
      ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M i) ∧
      ‖m i t * fsv s t‖ ≤ ‖m i t0 * fsv s t0‖ + 1 := by
    rw [Filter.eventually_all]
    intro i
    refine (Filter.eventually_of_mem (Metric.ball_mem_nhds t0 (hε' i)) fun t ht => hM i t ht).and ?_
    exact ((hac i).norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun t ht => ht.le
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ, hδ, (K : ℝ) * ∑ i, (‖m i t0 * fsv s t0‖ + 1) ^ 2 * M i, fun t ht => ?_⟩
  have hP := hδP t ht
  have hvlc : ∀ i, wOp X l (ab i) (Wn Ψ) ∈ lcSub P.k P.r z z' π π' := fun i => jsl_wOp_lc X l (ab i) _ hΦlc

  have hx : ∀ (c' : Cf P.r l.succ) (g : Mx P.k P.r),
      (wOp X l js Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g =
        ∑ i, (m i t * fsv s t) •
          (wOp X l (ab i) (Wn Ψ) : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g := by
    intro c' g
    by_cases hxo : glue l.succ (Function.update c l t) c' ∈ OmX P.r
    · have e := hE (Wn Ψ) _ hxo g
      rw [hΨeq, jsl_glue_self] at e
      exact e
    · have h0 : ∀ w : RadSp P.k P.r z z' π π',
          (w : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g = 0 :=
        fun w => radSp_zero_off w (x := (glue l.succ (Function.update c l t) c', g)) (fun h => hxo h.1)
      rw [h0]
      simp only [h0, smul_zero, Finset.sum_const_zero]
  have hpt : ∀ c' : Cf P.r l.succ,
      ‖wtI l.succ c' * pairAt μ (wOp X l js Ψ) (wOp X l js Ψ) (glue l.succ (Function.update c l t) c')‖ ≤
        (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ))
          (wOp X l (ab i) (Wn Ψ)) (glue l.succ (Function.update c l t) c')‖ := by
    intro c'
    have := jsl_pairAt_comb_le μ hμ (fun i => m i t * fsv s t) (wOp X l js Ψ) (fun i => wOp X l (ab i) (Wn Ψ))
      hvlc _ (hx c')
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left this (norm_nonneg _)).trans (le_of_eq ?_)
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [norm_mul]
    ring
  have hb : Integrable (fun c' : Cf P.r l.succ => (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 *
      ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ))
        (glue l.succ (Function.update c l t) c')‖) :=
    (integrable_finsetSum _ fun i _ => ((hP i).1.1.norm.const_mul _)).const_mul _
  refine ⟨?_, ?_⟩
  · unfold LevelSquareIntegrable
    exact hb.mono' ((wtI_measurable l.succ).aestronglyMeasurable.mul
      (pairAt_measI μ l.succ _ _ _).aestronglyMeasurable) (ae_of_all _ hpt)
  · have hfs : ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤
        (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ := by
      unfold fs
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hb (ae_of_all _ hpt)).trans
        (le_of_eq ?_)
      rw [integral_const_mul, integral_finsetSum _ fun i _ => (hP i).1.1.norm.const_mul _]
      simp only [integral_const_mul, jsl_int_norm_self]
    refine hfs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hP i).2 2) (hP i).1.2 (norm_nonneg _) (by positivity)

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LettersPassPartialBessel
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section congr

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pbF_congr_D (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) (i : ℕ) (hi : i ≤ n) {c0 : ℂ} {r : ℝ}
    {H1 H2 : B.Mat k n → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k n, dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < r → H1 g = H2 g)
    {y : B.Mat k n} (hy : y ∈ B.GV k n) (hyD : dist (Dmin k n B0.z B0.z' y ⟨i, by omega⟩) c0 < r) :
    PBQ.pbF Bj B0 e H1 y = PBQ.pbF Bj B0 e H2 y := by
  rw [pbF_eq_TI, pbF_eq_TI]
  unfold TI
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, ite_eq_left hx]
    congr 2
    have hs : sE Bj e x ∈ Sset k n B0.z := hzS ▸ sE_mem_S Bj e x
    have hs1 : (1 : B.Mat k n) ∈ Sset k n B0.z' := Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k n B0.z'
    have hmem : sE Bj e x * y ∈ B.GV k n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hy
    have hD : Dmin k n B0.z B0.z' (sE Bj e x * y) ⟨i, by omega⟩ = Dmin k n B0.z B0.z' y ⟨i, by omega⟩ := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds k n B0.z B0.z' B0.z_mem B0.z'_mem _ hs 1 hs1 y ⟨i, by omega⟩
      rwa [Matrix.mul_one] at this
    unfold PBG.Kr
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBG.ae_inR B0] with ξ hξ
    have hG : sE Bj e x * y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k n :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hmem hξ.2.1) hξ.1.1
    rw [h _ hG (by rw [Formalism.FourierDecayAlt.P.PBG.dmin_pR B0 hξ, hD]; exact hyD)]
  · simp [gI, hx]

end congr

section words

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pbWords_core (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (Cs : Set (B.Mat k n))
    (hL : ∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g)
    (hCs : IsCompact Cs) (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) (U : Set (B.Mat k n)) (hU : IsOpen U)
    (hD : ∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) (hP : Proper Bj B0 e Cs U) :
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y
  | [], _, _, _, _ => rfl
  | l :: w, ew, y, hyU, hy => by
    have ih := pbWords_core Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w (fun a => ew a.succ)
    set H' := D.uwG k n B0.z B0.z' H i hi w (fun a => ew a.succ) with hH'
    have hCsClosed : IsClosed Cs := IsCompact.isClosed hCs
    have hLocSupp :
        (∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 →
          CapelliWordSumExpansion.Loc ⊤ H' g) ∧
        (∀ g ∈ B.GV k n, g ∉ Cs → H' g = 0) :=
      uwG_locSupp (k := k) (n := n) (E := Wq →L[ℂ] Wp) (H := H) (Cs := Cs)
        B0.z B0.z' i hi hCsClosed hL hS w (fun a => ew a.succ)
    set c0 := Dmin k n B0.z B0.z' y ⟨i, by omega⟩ with hc0
    have hc0ne : c0 ≠ 0 := hD y hyU
    have hCutoff :
        ∃ Ht : B.Mat k n → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k n) Ht ∧
          (∀ g ∈ B.GV k n, g ∉ Cs → Ht g = 0) ∧
          ∀ g ∈ B.GV k n, dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4 →
            Ht g = H' g :=
      cutoff_exists (H := H') (Cs := Cs) (c0 := c0) B0.z B0.z' i hi hLocSupp.1 hLocSupp.2 hc0ne
    rcases hCutoff with ⟨Ht, hHt, hHtS, hHtE⟩
    have hDc : Continuous (fun g : B.Mat k n => Dmin k n B0.z B0.z' g ⟨i, by omega⟩) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin B0.z B0.z' ⟨i, by omega⟩).continuous
    set W0 := {g : B.Mat k n | dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4} with hW0
    have hW0o : IsOpen W0 := isOpen_lt (hDc.dist continuous_const) continuous_const
    have hyW0 : y ∈ W0 := by
      show dist c0 c0 < ‖c0‖ / 4
      rw [dist_self]; have := norm_pos_iff.mpr hc0ne; positivity
    have hV0o : IsOpen (U ∩ W0) := hU.inter hW0o

    have e1 : ∀ g ∈ U ∩ W0, g ∈ B.GV k n →
        D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w (fun a => ew a.succ) g = PBQ.pbF Bj B0 e Ht g := by
      intro g hg hgG
      rw [ih g hg.1 hgG]
      exact pbF_congr_D Bj B0 e hzS i hi (fun g' hg' hd => (hHtE g' hg' hd).symm) hgG hg.2
    have hvK : VanishL Bj e (PBG.Kr B0 Ht) U := vanish_kr Bj B0 e hHtS hP
    show D.vLet k n B0.z B0.z' i hi l (ew 0) (D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w fun a => ew a.succ) y =
      PBQ.pbF Bj B0 e (D.vLet k n B0.z B0.z' i hi l (ew 0) H') y
    rw [Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_congr B0.z B0.z' i hi l (ew 0) hV0o e1 y ⟨hyU, hyW0⟩ hy,
      vLet_pb Bj B0 e hzS hHt hCs hHtS hU hvK i hi l (ew 0) hyU hy hc0ne]
    refine pbF_congr_D Bj B0 e hzS i hi (r := ‖c0‖ / 4) (c0 := c0) (fun g hg hd => ?_) hy hyW0
    exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_congr B0.z B0.z' i hi l (ew 0) hW0o (fun g' hg' hg'G => hHtE g' hg'G hg') g hd hg

end words

theorem _root_.Formalism.FourierDecayAlt.P.letters_pass_partial_bessel : PbWords := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w ew y hyU hy
  exact pbWords_core Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w ew y hyU hy

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceTopZero
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSl0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  refine ⟨hγ, fun l hl => ?_, ?_⟩
  · have hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2)) := Fin.ext (by simp only; omega)
    subst hl0
    unfold Dmin
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  · have e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ := by
      unfold Gf Q.GGl Dmin
      rw [Matrix.det_fin_zero, Matrix.det_fin_one]
      simp only [Complex.normSq_one, mul_one]
      rfl
    rw [e]
    exact hG

theorem sliceTop_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : P.r = 0) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm := om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hr
  subst hr
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil
  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]
  have hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀ := fun v => funext fun q => (hE.false q).elim
  refine ⟨?_, ?_⟩
  · rw [hvol]
    refine (integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [hxe v]
  · have hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) =
        CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ := by
      rw [hvol, integral_dirac]
      unfold PBQ.ellH
      have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
      have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
        unfold U.subS
        exact Finset.sum_of_isEmpty _
      rw [hs]
      simp [Formalism.FourierDecayAlt.G.psi]
    rw [hone]
    have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G := by
      funext y
      simp only [D.castF]
      refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_
      exact congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
    have hCpt : KB.CptCoef (p.T.bs 0) G := hG.1
    have hL := SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ
      (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)
    have hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ := by
      unfold CutEX.xT U.mMap
      rw [SliceIntegralLemmas.block_three_zero_size_eq]
      exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ
    rw [e3, hL]
    unfold CutEX.pbTop PBQ.pbT
    rw [hx, SliceIntegralLemmas.pbF_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    rfl

end Formalism.FourierDecayAlt.P.CutEXSl0
end
end

