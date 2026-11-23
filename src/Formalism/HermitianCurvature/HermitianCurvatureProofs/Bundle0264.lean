module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0263
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0262
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0260
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0217
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0233
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0261
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0225
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0254
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralSobolevSecondOrder
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSWordNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothTruncationInduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0259
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXSliceTop
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_integral_level_reduction (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))) volume ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  have hz1 : B0.z = liftVec k p ρ Bj.z := by rw [← hz, JCTx5.castV_rfl]
  have hz1' : B0.z' = liftVec k p ρ Bj.z' := by rw [← hz', JCTx5.castV_rfl]
  have hπ1 : ∀ y, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Dx2.MN.castM_rfl, Dx2.Tower.lev_eq_embG]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    refine hHc.mono ?_
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Ux3.zhDmin]
    exact hx.2
  obtain ⟨hi, heq⟩ := SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz1' hπ1 hW' hW0' hNj hN0 g hg H hHc' R hR
  refine ⟨?_, ?_⟩
  · simpa only [Dx2.MN.castM_rfl] using hi
  · rw [JCTx5.castV_rfl, JCTx5.castV_rfl, hz1, hz1']
    simp only [Dx2.MN.castM_rfl]
    exact heq

end gen

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_gen (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hG : B.CkOn ⊤ (B.GV P.k P.r) G) (R : ℝ) (hR : ∀ x ∈ B.GV P.k P.r, G x ≠ 0 → B.gN x ≤ R)
    (h : C.LPt) (j : ℕ) (hjr : j ≤ P.r) (hh : D.IsLocPt h j) (hj1 : 1 ≤ j) (γ : B.Mat P.k (P.r - j))
    (hOm : γ ∈ JF.Om P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z') :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ)))) ∧
    B.JF (p.T.bs j) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
      ∫ v, PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ))) := by
  obtain ⟨hh1, rfl⟩ := hh
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hzj := p.T.z_lev (D.ptSize h) hjr
  have hzj' := p.T.z'_lev (D.ptSize h) hjr
  have hπj : ∀ y, (p.T.bs (D.ptSize h)).π' y = p.T.base.π' (D.castM e (ιLev P.k _ _ y)) :=
    fun y => p.T.π'_lev _ hjr y
  obtain ⟨hWj, hW'j, hNj⟩ := p.hT (D.ptSize h) hjr
  obtain ⟨hW0, hW'0, hN0⟩ := p.hT 0 (Nat.zero_le _)
  have hW0' : p.T.base.μW' = (p.T.bs (D.ptSize h)).μW'.map (PBM.levMt (D.ptSize h) (P.r - D.ptSize h) e) :=
    PBM.haar_lev _ _ e _ _ hzj' _ _ p.T.base.haarW' (p.T.bs _).haarW' hW'0 hW'j
  have hGc : ContinuousOn G {x | x ∈ B.GV P.k P.r ∧
      Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    (PBE.ckOn_continuousOn' subset_rfl hG).mono fun x hx => hx.1
  obtain ⟨H1i, H1e⟩ := slice_integral_level_reduction e hj1 (D.ptPerm h) (D.ptDiag h) (CutHB.ptDiag_ne ⟨hh1, rfl⟩)
    (p.T.bs (D.ptSize h)) p.T.base hzj hzj' hπj hW'j hW0' hNj hN0 γ hOm G hGc R hR
  have hcf : ∀ (e' : P.r - D.ptSize h = P.r - D.ptSize h) (F : B.Mat P.k (P.r - D.ptSize h) → (Wq →L[ℂ] Wp)),
      D.castF e' F = F := fun e' F => by
    funext x
    simp only [D.castF, Dx2.MN.castM_rfl]
  refine ⟨?_, ?_⟩
  · simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    simp only [SliceIntegralLemmas.psiH] at H1i
    exact H1i
  · rw [hcf, D.sliceAt, dite_eq_left hjr]
    simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact H1e

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  have h0 : ∀ (hl : 0 < 0 + 2), Dmin k 0 z z' γ ⟨0, hl⟩ = 1 := by
    intro hl
    simp [Dmin]
  have h1 : Dmin k 0 z z' γ (Fin.last (0 + 1)) = Q.zetaL k 0 z z' (Fin.last 0) γ := by
    rw [PBI.zetaL_eq_zhat]
    simp [Dmin, Matrix.det_unique]
  refine ⟨hγ, ?_, ?_⟩
  · intro l hl
    have hl0 : l = ⟨0, by omega⟩ := Fin.ext (by simpa using hl)
    rw [hl0, h0]
    exact one_ne_zero
  · unfold Gf
    rw [h1, h0]
    simpa [Q.GGl] using hG

end top

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem sliceTop_pos (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : 1 ≤ P.r) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm : γ ∈ JF.Om P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' :=
    om_zero (Nat.sub_self _) _ _ γ hγ hGG
  obtain ⟨R, hR⟩ := hG.1.2.1
  exact slice_gen P p G hG.1.1 R hR h P.r le_rfl hh hr γ hOm

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P

theorem slice_top_exhaustion : CutEX.SliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh γ hγ hGG
  rcases Nat.eq_zero_or_pos P.r with h0 | h1
  · exact CutEXSl0.sliceTop_zero Wp Wq P p h0 G hG h hh γ hγ hGG
  · exact CutEXSlice.sliceTop_pos Wp Wq P p h1 G hG h hh γ hγ hGG

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLoc
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerD Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain in
theorem jSRadLoc_of (hU : FamCCUnif) : JSRadLoc := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε hε G hN hGc Φ hlc hΦ c hc js hjs t0 ht0
  have hr0 : 0 < P.r := by have := l.isLt; omega
  obtain rfl : l = ⟨0, hr0⟩ := Fin.ext hl
  obtain ⟨Tw, hNw, e1, e2, e3, e4, Di, Xi, μi, Li, sti, κ, hDiEq, hκ, hDi, hall⟩ :=
    Formalism.FourierDecayAlt.P.level_transport_unitary Wp Wq P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' ⟨1, by omega⟩
  subst e1 e2 e3 e4
  subst hDiEq
  have hj : 0 + 1 ≤ P.r := by omega
  have hP : IsPlace P Tw.base.z Tw.base.z' Tw.base.π Tw.base.π' := hD.1
  have hPj := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P Tw ⟨0, by omega⟩ hP
  have hPs := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P Tw ⟨0 + 1, by omega⟩ hP
  obtain ⟨κ0, hκ0⟩ := Formalism.FourierDecayAlt.P.jacquet_scaling P.k P.r Wp Wq D Tw.base hz hz' hπ hπ'

  set G0 : B.Mat P.k (P.r - 0) → (Wq →L[ℂ] Wp) := fun g => κ0 • G g with hG0
  have hG0ok : JFOKCpt (JC.parLev P 0) (Tw.bs 0).z (Tw.bs 0).z' G0 := by
    have hck : B.CkOn ⊤ (B.GV P.k (P.r - 0)) G0 := by
      intro g₀ hg₀
      obtain ⟨U, f', hU', hgU, hcf, hff⟩ := hN.1 g₀ hg₀
      exact ⟨U, fun g => κ0 • f' g, hU', hgU, hcf.const_smul κ0, fun g hg hgG => by
        simp only [hG0]; rw [hff g hg hgG]⟩
    have hz0 : ∀ g ∈ B.GV P.k (P.r - 0), g ∉ tsupport G → G0 g = 0 := fun g _ hg => by
      simp only [hG0]; rw [image_eq_zero_of_notMem_tsupport hg, smul_zero]
    refine ⟨⟨fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hck hGc hz0 A m, ε, hε, fun g hg hne => ?_⟩, ?_⟩
    · have hne' : G g ≠ 0 := fun h => hne (by simp only [hG0]; rw [h, smul_zero])
      have := hN.2.2 g hg hne'
      rwa [hz, hz'] at this
    · exact HasCompactSupport.intro hGc (fun g hg => by simp only [hG0]; rw [image_eq_zero_of_notMem_tsupport hg, smul_zero])
  have hΦ0 : IsRadJF (JC.parLev P 0) (Tw.bs 0).z (Tw.bs 0).z' (Tw.bs 0).π (Tw.bs 0).π' (Tw.bs 0) G0 Φ := by
    intro (x : (Fin P.r → ℂ) × Mx P.k P.r) hx
    have e : B.JF Tw.base G0 = κ0 • B.JF Tw.base G := by
      funext h
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul (Bs := Tw.base) κ0 G h
    have h2 : resG P.k P.r (Fin.last P.r) (B.JF D G) x.1 x.2 =
        resG P.k P.r (Fin.last P.r) (B.JF Tw.base G0) x.1 x.2 := by
      rw [hκ0 G, e]
    exact (hΦ x hx).trans h2
  have hC0 : CutSH.InC Tw 0 hj Φ :=
    CutSH.inC_seed Formalism.FourierDecayAlt.P.cell_compatibility_identity Formalism.FourierDecayAlt.P.slice_family_good
      CutSH.slice_family_orbital hP hNw hPj hPs G0 hG0ok Φ hΦ0
  have hW : ∀ js : List (Fin 6), CutSH.InC Tw 0 hj (wOp X ⟨0, hr0⟩ js Φ) := by
    intro js
    induction js with
    | nil => simpa [wOp] using hC0
    | cons j js ih =>
      have e : wOp X ⟨0, hr0⟩ (j :: js) Φ = X.op ⟨0, hr0⟩ j (wOp X ⟨0, hr0⟩ js Φ) := by
        simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [e]
      exact Formalism.FourierDecayAlt.P.operator_class_closed Wp Wq P Tw hP hNw 0 hj hPj hPs X j _ ih
  obtain ⟨Gj, hGj, hRep⟩ := hW js
  set K : Set ℂ := Metric.closedBall t0 (‖t0‖ / 2) with hKdef
  have hK : IsCompact K := isCompact_closedBall _ _
  have hn0 : 0 < ‖t0‖ := norm_pos_iff.2 ht0
  have hK0 : ∀ t ∈ K, t ≠ 0 := fun t ht h0 => by
    rw [h0, hKdef, Metric.mem_closedBall, dist_zero_left] at ht
    linarith
  obtain ⟨c4, hc4⟩ := hU Wp Wq P Tw 0 Gj hGj K hK hK0 (B.AB P.k (P.r - (0 + 1))) 4
  obtain ⟨CR, hCR, hRB⟩ := Formalism.FourierDecayAlt.P.radial_beta_pos Wp Wq P Tw ⟨1, by omega⟩ μi hDi.2.1
  obtain ⟨-, -, -, ⟨CB, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k (P.r - (0 + 1)) Wp Wq (Tw.bs (0 + 1))
    (B.AB _ _) le_rfl
  refine ⟨‖t0‖ / 2, by positivity, κ⁻¹ * CR⁻¹ * (|CB| * |c4| * |c4|), fun t ht => ?_⟩
  have htK : t ∈ K := Metric.ball_subset_closedBall ht
  have ht0' : t ≠ 0 := hK0 t htK
  obtain ⟨Tt, ⟨hform, -⟩, hpair⟩ := hall (Function.update c ⟨0, hr0⟩ t) (fun l' hl' => by
    have e : l' = ⟨0, hr0⟩ := Fin.ext (by simp at hl'; omega)
    subst e
    simpa using ht0')

  set Ψ := wOp X ⟨0, hr0⟩ js Φ with hΨdef
  have hTΨ : ∀ x ∈ DomR P.k (P.r - (0 + 1)) (Tw.bs (0 + 1)).z (Tw.bs (0 + 1)).z',
      (Tt Ψ : Fn P.k (P.r - (0 + 1)) (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG P.k (P.r - (0 + 1)) (Fin.last _) (B.JF (Tw.bs (0 + 1)) (Gj t)) x.1 x.2 := by
    intro x hx
    rw [hform]
    have hg : glue ⟨1, by omega⟩ (Function.update c ⟨0, hr0⟩ t) (PTie.shiftCf ⟨1, by omega⟩ x.1) =
        CutSH.cc 0 hj t x.1 := by
      funext l'
      rcases Nat.eq_zero_or_pos l'.val with h | h
      · have e : l' = ⟨0, hr0⟩ := Fin.ext h
        subst e
        simp [glue, CutSH.cc, consC]
      · have hne : l' ≠ ⟨0, hr0⟩ := fun e => by rw [e] at h; simp at h
        have h1 : (1 : ℕ) ≤ l'.val := h
        simp [glue, CutSH.cc, consC, PTie.shiftCf, h1, Nat.pos_iff_ne_zero.mp h]
    rw [hg]
    exact hRep t ht0' x hx
  obtain ⟨⟨hInCC, εt, hεt, hεG⟩, -⟩ := CutSH.family_orbital_valid Wp Wq P Tw 0 Gj hGj t ht0'
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (0 + 1))) (Gj t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU', hmem, hf, hfe⟩ := hGj.1 t ht0' γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (0 + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU'.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  have hNice : JC.NiceCoef (Tw.bs (0 + 1)) εt (Gj t) := ⟨hck, hInCC, hεG⟩
  have hL2 : LevelSquareIntegrable μi 0 (Tt Ψ) 0 := by
    have h := Formalism.FourierDecayAlt.P5.HerC.level_zero_form_integrable_compact (S := Empty) (Tw.bs (0 + 1)) μi hDi.2.1 (fun _ => Gj t) (fun _ => Gj t)
      (fun _ => Tt Ψ) (fun _ => Tt Ψ) (fun _ => hInCC) (fun _ => hInCC) (fun _ => hTΨ) (fun _ => hTΨ) 0
    unfold LevelSquareIntegrable
    simpa [wtI] using h
  refine ⟨level_one_square_integrable_of_transport μ ⟨0, hr0⟩ c t μi Tt κ hκ hpair Ψ 0 hL2, ?_⟩
  rw [fs_tr μ ⟨0, hr0⟩ c t μi Tt κ hκ hpair Ψ Ψ]
  have hform0 : (∫ c'' : Cf (P.r - (0 + 1)) 0, wtI 0 c'' * pairAt μi (Tt Ψ) (Tt Ψ)
      (glue 0 (shiftV (Fin.succ ⟨0, hr0⟩) (Function.update c ⟨0, hr0⟩ t)) c'')) =
      form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 := by
    unfold form
    congr 1
    funext c''
    have eg : glue 0 (shiftV (Fin.succ ⟨0, hr0⟩) (Function.update c ⟨0, hr0⟩ t)) c'' = glue 0 0 c'' := by
      funext l'; simp [glue]
    rw [eg]
    simp [wtI]
  have hβ := hRB 0 (fun _ => Gj t) (fun _ => Gj t) (fun _ => Tt Ψ) (fun _ => Tt Ψ) εt hεt (fun _ => hNice)
    (fun _ => hNice) (fun _ => hTΨ) (fun _ => hTΨ)
  have hβ' : B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t) = (CR : ℂ) * form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 := by
    convert hβ using 1
    · simp
    · rfl
  have hb := (hB1 (Gj t) (Gj t) c4 c4 (hInCC _ 5) (hInCC _ 5) (hc4 t htK) (hc4 t htK)).2.2
  erw [hform0]
  have hf : form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 = (CR : ℂ)⁻¹ * B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t) := by
    rw [hβ']
    have : (CR : ℂ) ≠ 0 := by exact_mod_cast hCR.ne'
    field_simp
  rw [hf, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hκ.le,
    Real.norm_of_nonneg hCR.le, mul_assoc]
  gcongr
  calc ‖B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t)‖ ≤ CB * c4 * c4 := hb
    _ ≤ |CB| * |c4| * |c4| := by
      have := abs_mul_abs_self c4
      calc CB * c4 * c4 = CB * (c4 * c4) := by ring
        _ ≤ |CB * (c4 * c4)| := le_abs_self _
        _ = |CB| * |c4| * |c4| := by rw [abs_mul, abs_mul, mul_assoc]

theorem spectral_radial_locality : JSRadLoc := jSRadLoc_of family_uniform_compact_convergence

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceDone
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem jSliceGenC_of_radLoc (hR : JSRadLoc) : JSliceGenC :=
  jSliceGenC_of_sob2_meas_locality spectral_sobolev_second_order spectral_measurability (jSL2Loc_of spectral_word_normal_form hR)

theorem leibnizCls_of_radLoc (hR : JSRadLoc) : LeibnizCls :=
  leibnizCls_of_jSliceC (jSliceGenC_of_radLoc hR)

theorem densSmoothCls_of_radLoc (hR : JSRadLoc) : DensSmoothCls :=
  densSmoothCls_of_jSliceC (jSliceGenC_of_radLoc hR)

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SideOnePositive
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem side_one_positive : CutHB.Side1Pos :=
  LevelPointCoordinates.side1Pos_of smooth_truncation_induction smooth_truncation_exists (SliceIntegralLemmas.side0Pos_of'' proper_left_variables_domain)
    letters_pass_partial_bessel proper_left_variables_domain

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SideZeroOfLocalProperness
section
namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt

theorem side_zero_of_local_properness (hPr : ProperLeftVariablesDomain) : CutHB.Side0 :=
  CutHB.side_zero_of_positive_and_zero (side0Pos_of'' hPr) (side0Zero_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts)

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepSquare
section
namespace Formalism.FourierDecayAlt.P5.HerD

theorem thmPActualCpt_of_stepExp0 (h0 : StepExp0) : ThmPActualCpt :=
  theorem_P_compact_of_step_density Formalism.FourierDecayAlt.P.level_transport_hermitian h0

end Formalism.FourierDecayAlt.P5.HerD
end

