module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEvREqFjAnLie
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
open GlobalTheory.ArcCoeff

namespace GlobalTheory.ArcCoeffAt

theorem coeff_evR_eq_fj_anLie : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), AnLie Uw.F Ha.i (Ha.Pw w₁) (U.un k x) z ∧ (∀ v, Uw.Pm k x (gm v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (gm v) (gm v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (gm t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ th ξ ν₀ jj a' n hEv hσ hU halg hχ hmono hpush hth
    hrk hξ0 hβ hD hTr w₁ hw₁
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e) th hth
  obtain ⟨k, ξ', sE, hiso, hbe, hpos, hlev, hdict⟩ :=
    GlobalTheory.ArcFlow.holArc_eq_flow_orbit hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha hσ hU hrk ξ hξ0 w₁ hw₁
  obtain ⟨C₀, hC₀, hC₀', hcov⟩ := GlobalTheory.LatticeCovolumeL2.det_im_eq_covol E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hσ hU hiso hrk
  set B : ℝ := ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w₁).map Complex.im).submatrix
    (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ with hBdef
  have hB : 0 < B := by
    have h1 := ((Θ.pos w₁ hw₁).2.submatrix (e := fun k : {k // k ∉ Θ.S} => k.1) Subtype.val_injective).det_pos
    have h2 := norm_pos_iff.2 Θ.κ_ne
    positivity
  refine ⟨k, ξ', sE, B * C₀, hiso, hbe, hpos, hlev, mul_pos hB hC₀, fun v hv => ?_, fun e z y hy hz => ?_⟩
  · rw [_root_.GlobalTheory.AbelianPartNorm.norm_eq hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w₁ v hw₁ hv]
    exact mul_le_mul_of_nonneg_left hC₀' hB.le
  have hzt := GlobalTheory.T.arc_letter_analyticVectors_independent_blockType hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha y e th z hσ halg (GlobalTheory.ThetaShiftProofs.mono_j Y hmono) hy hz
  obtain ⟨x, hx, L, gm, hEF, hLz, ⟨t, ht, htξ⟩, hflow⟩ := hdict z hzt
  obtain ⟨T', hT'⟩ := GlobalTheory.T.hasSum_sectionValue_arc_framedPoint hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha y e th Θ z hEv halg hχ hmono hpush hth hy hz
  set K : ℝ := (B * C₀ * ∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x with hKdef
  have htt : ∀ x' ∈ (U.X k).dom, 0 < ∏ τ, ((U.X k).tt ξ' x' τ)⁻¹ := fun x' hx' =>
    Finset.prod_pos fun τ _ => inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso hx' τ)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (mul_pos (mul_pos hB hC₀) (htt x hx)) _)
    (MinimumGrowthBounds.nfac_pos _ _ hx)
  let fl : ℂ → Frame (U.X k).Ψ r := fun w => (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x
  have key : ∀ w : ℂ, ∃ cw : ℂ, max Ha.T T' < w.im → ∀ F ∈ sec Xo c a' n,
      HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (cw * rdU U F k (fl w)) ∧
        ‖cw * rdU U F k (fl w)‖ = K * ‖rdU U F k (fl w)‖ := by
    intro w
    by_cases hw : max Ha.T T' < w.im
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
    obtain ⟨hxw, hPm, hlie⟩ := hflow w hw1
    obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ z hσ hzt w hw1
    obtain ⟨s, hs⟩ := frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw1) _ _ z hlie hyw.1
    have hv := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w yw hw1 hyw.1.1 hyw.2
    have hoff : (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) =
        (((Θ.τ w₁).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) := by
      ext i j
      exact congrArg Complex.im (tau_col_const Ha Θ w w₁ i.1 j.1 j.2)
    rw [hcov w ⟨_, hxw⟩ L gm hw1 hPm hEF ⟨t, fun v' hv' => by
      have := ht v'
      rwa [hv', map_zero, neg_eq_zero] at this, htξ⟩, hoff, ← _root_.mul_assoc, ← _root_.mul_assoc, ← hBdef] at hv
    refine ⟨toC s ^ n, fun _ F hF => ?_⟩
    obtain ⟨e1, e2⟩ := evR_eq_and_norm hL hL2 U Uw hEv hσ hU k ⟨_, hxw⟩ yw s _ hs Ha.i _ (Ha.period w hw1) hyw.1.1 hv
      a' n F hD hF
    have hsum := hT' w hw2 yw hyw a' n F hF
    rw [e1] at hsum e2
    refine ⟨hsum, e2.trans ?_⟩
    have hn := GlobalTheory.ArcQ.nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hD.2 hiso x hx _ hxw
    rw [hKdef, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hxw).le, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hx).le]
    dsimp only [fl]
    linear_combination ((B * C₀) ^ ((n : ℝ) / 2) * ‖rdU U F k (fl w)‖) * hn
  choose cw hcw using key
  have hfl : Differentiable ℂ fl := (FlowMeanContinuity.flow_differentiable (U.X k) ξ' x).comp (by fun_prop)
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.exists_const_ratio_of_norm_eq {F // F ∈ sec Xo c a' n} (max Ha.T T') K
    (fun F w => cw w * rdU U F.1 k (fl w)) (fun F w => rdU U F.1 k (fl w)) cw hK
    (fun F => ⟨differentiableOn_of_hasSum _ _ _ fun w hw => (hcw w hw F.1 F.2).1,
      (hU.2.2.2.2.1 a' n hD F.1 F.2 k).1.comp hfl.differentiableOn
        fun w hw => (hflow w (max_lt_iff.1 hw).1).1⟩)
    (fun F w hw => ⟨rfl, (hcw w hw F.1 F.2).2⟩)
  refine ⟨⟨x, hx⟩, κ, L, gm, ?_, fun v => ?_, hEF, hLz, ⟨t, ht, htξ⟩, hκ, fun F hF hbdd => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hflow w₁ hw₁
    have e0 : (⟨_, h1⟩ : (U.X k).dom) = ⟨x, hx⟩ := Subtype.ext (by
      simp only [sub_self, zero_mul]
      exact EmbeddingHermitianPairs.flow_zero _ _ _)
    rwa [e0] at h3
  · obtain ⟨h1, h2, -⟩ := hflow w₁ hw₁
    rw [← h2 v]
    congr 3
    simp only [sub_self, zero_mul]
    exact (EmbeddingHermitianPairs.flow_zero _ _ _).symm
  · refine coeff_eq_of_betaAt (U.X k) hbdd hiso hx ξ l.M' a.be
      (fun y z => (dvd_mul_left _ 2).trans (a.be_dvd y z)) hβ hbe hpos (hTr k) (hlev _) κ w₁ _ (max Ha.T T')
      fun w hw => ?_
    exact hκ' ⟨F, hF⟩ w hw ▸ (hcw w hw F hF).1

end GlobalTheory.ArcCoeffAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbit
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem tieC_of_onOrbit : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (ξC : Module.Dual ℤ aC.D₀.X), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → l.A = 1 → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → (∀ y, ξC (Λ.eX y) = ξ y) → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), TieC Uw (aC.restrict β) ξC k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x aC Λ ξC hσ hU hξ hx hA gam ξ hO hξC hL O _ β Y χ W Ha
  let := H.starRing
  let Λ' : GtAn₀ (aC.restrict β) := ⟨Λ.toGtDict, Λ.be_eq⟩
  obtain ⟨g₁, h₁, e1, e2, e3, e4⟩ := GlobalTheory.T.holomorphicArc_agrees_analyticDictionary hK E H Dw l Xo c σ O β Y (aC.restrict β) χ W Uw.g _ Uw.F Ha Λ'
  obtain ⟨o1, ⟨t', o2, o3⟩, T₀, o4⟩ := hO
  have hw : max Ha.T T₀ < (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I) = w at hw
  obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
  obtain ⟨s, hs, h, hh⟩ := o4 w hw2
  let gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La := g₁.trans gam.symm
  let L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ) := h₁.trans h.symm
  have hgm : ∀ u, gam (gm u) = g₁ u := fun u => gam.apply_symm_apply _
  have hEF : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gm u) (gm v) = (Uw.F.Di Ha.i).EF u v := fun u v => by
    rw [← o1, hgm, hgm]; exact e4 u v
  have hP : ∀ u, Uw.Pm k ⟨_, hs⟩ (gm u) = L (Ha.Pw w u) := fun u => by
    apply h.injective
    rw [hh, hgm]
    exact (e3 w u).symm.trans (h.apply_symm_apply _).symm
  have hpq : 1 ≤ Dw.p + Dw.q := by
    rw [← hU.1]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (Subsingleton.elim _ _) hξ.2.2
    · exact hr
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e
  have hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.M • e := by
    intro v hv
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelM v hv
    have hq : q = Λ.toGtDict.qk l.M (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      have h0 : h₁ (Ha.P₀ (Uw.F.t Ha.i v)) = Λ.A.P0 (g₁ (Uw.F.t Ha.i v)) := by
        have := e3 0 (Uw.F.t Ha.i v)
        rw [Ha.Pw_eq, zero_smul, add_zero] at this
        exact this.trans (by rw [AnArc.Pw_apply, zero_smul, add_zero])
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.eta v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.eta v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hL v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add (f := _), map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  obtain ⟨p1, p2⟩ := GlobalTheory.ArcCM.point_exp_eq_of_isometry hK E H Dw l Xo _ Uw.g _ Uw.F Ha.i (Uw.ik k) (Ha.Pw w) (Uw.Pm k ⟨_, hs⟩) gm L hpq hσ hty hA
    (Ha.period w hw1) (Uw.period k _) hEF hlev hP
  refine ⟨w, s, hs, L, gm.symm t', t', hw1, fun v' => ?_, o2, ?_, p1, p2⟩
  · rw [← hEF, gm.apply_symm_apply, o3, ← hξC, hgm, ← e2]
    rfl
  · rw [← hP, gm.apply_symm_apply]

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobiStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCoeff_sectionValue_arc_eq_fourierJacobi : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  first | exact @GlobalTheory.ArcCoeff.coeff_evR_eq_fj | exact GlobalTheory.ArcCoeff.coeff_evR_eq_fj | (intros; apply GlobalTheory.ArcCoeff.coeff_evR_eq_fj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisation
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.FinLoc


open GlobalTheory.IntModelExists GlobalTheory.Frames in
theorem exists_intModel_heq : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (b : c.V Wl →+* Tv.V) (aw : ArcIn Dw l (c.V Wl).subtype Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io d.a.D₀ aK.D₀), Yw.N4 → ArcLieBasis d.W d.e → InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict (c.V Wl).subtype) pw → InBC io d.a aK pK → ∃ M : IntModel d Tv io Wl, M.b = b ∧ HEq M.aw aw ∧ M.aK = aK ∧ HEq M.pw pw ∧ HEq M.pK pK ∧ M.γ ≠ 0 ∧ (∀ τ, (M.g τ).det ≠ 0) ∧ ∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew := by
  intro hL hL₂ hU hL₅ E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl Yw b aw aK pw pK hN hd hw hK
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap Tv.V Tv.Fr) := IsFractionRing.injective _ _
  have hb : ∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (x : c.F)) := fun x =>
    (RingHom.congr_fun hw.1 x).symm
  let ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V) := fun τ => b.comp (embV c Wl τ)
  have hρ : ∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = io (algebraMap c.F K₁ (embK c τ x)) := fun τ x => hb _

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V b ϖ aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨ew, -, hew⟩ := _root_.GlobalTheory.ConstBasis.exists_arcBasis hL hL₂ E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ (io.comp (algebraMap c.F K₁))
    hw.1 hρ (exists_values c Wl)

  obtain ⟨W₁, e₁, l₁, b₁⟩ := exists_arcBasis_baseChange hL hL₂ hU hL₅ hinj hw W₀ hew
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (aK.restrict (c.V d.Wp).subtype) pK := ⟨rfl, hK.2⟩
  have hd' : ArcBasis (Y := d.Y) d.W (fun τ => (algebraMap c.F K₁).comp (embK c τ)) d.e := hd
  obtain ⟨W₂, e₂, l₂, b₂⟩ := exists_arcBasis_baseChange hL hL₂ hU hL₅ io.injective hK' d.W hd'
  have hρ' : (fun τ => io.comp ((algebraMap c.F K₁).comp (embK c τ))) = fun τ => (algebraMap Tv.V Tv.Fr).comp (ρ τ) :=
    funext fun τ => RingHom.ext fun x => (hρ τ x).symm
  rw [hρ'] at b₂
  obtain ⟨p, p₁, p₂, p₃⟩ := exists_self aK.D₀ aK.gen
  have b₂' := (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ d.Y Tv.Fr _ _ _ W₂ _ e₂ b₂).1 _ _ Yw _ _ _ W₁ p e₂
    (fun x y => (p₂ _).trans (congrArg (x • ·) (p₂ y).symm)) (fun x => p₁ _) (fun τ k => p₃ _)
  obtain ⟨g, hg, hge⟩ := exists_matrix hG W₁ b₁ b₂'
  have t₁ : ∀ τ k, GtTanR (e₁ τ k) := fun τ k => by
    obtain ⟨v, i, hv⟩ := b₁
    exact ((_root_.GlobalTheory.ConstLie.main hG E H Dw l Xo c _ _ Yw Tv.Fr _ _ _ W₁ (e₁ τ k)).2 _ (i τ k)).2 ((hv τ).1 k).1

  obtain ⟨thw, hthw, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange aw.D₀.P
  obtain ⟨-, -, -, x₁, z₁⟩ := (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ Yw Tv.V Tv.Fr b aw _ hinj _ hw.1).2
    (aK.restrict (c.V Wl).subtype) pw hw
  obtain ⟨-, -, -, x₂, z₂⟩ :=
    (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) io
      io.injective _ hK'.1).2
      (aK.restrict (c.V d.Wp).subtype) pK hK'
  obtain ⟨th₁, hth₁⟩ := (x₁ thw).exists
  obtain ⟨th₂, hth₂⟩ := (x₂ d.th).exists
  have nz : ThNZ d.th := by
    obtain ⟨_, _, _, _, h, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h
  obtain ⟨gm, hγ⟩ :=
    ((GlobalTheory.ThetaOverField.nonzero_generates hL hL₂ Tv.Fr aK.D₀ th₁).2.1 (z₁ _ _ hth₁ hthw) th₂).exists
  have hγ₀ : gm ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := (GlobalTheory.ThetaOverField.exists_ne_zero_iff aK.D₀ th₂).2 (z₂ _ _ hth₂ nz)
    refine hj ((hγ j).trans ?_)
    rw [constFn, map_zero, map_zero, zero_mul]
  exact ⟨⟨b, hb, ρ, hρ, aw, aK, pw, pK, hw, hK, thw, hthw, ew, gm, g, ⟨th₁, th₂, hth₁, hth₂, hγ⟩,
    ⟨e₁, e₂, l₁, l₂, t₁, hge⟩⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, hγ₀, hg,
    (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c _ _ Yw Tv.V b aw χ₀ W₀ ρ ew hew).2.1⟩

section Val

variable {K : Type} [Field K] [NumberField K]

theorem mem_range_of_le_one {w : HeightOneSpectrum (𝓞 K)} {T : CDVR} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa w T.V io e) {x : K} (hx : w.valuation K x ≤ 1) : io x ∈ Set.range (algebraMap T.V T.Fr) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have h1 : valV T.V (io x) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
  have h2 : WithZero.log (w.valuation K x) ≤ 0 := by
    simpa using (WithZero.log_le_log ((w.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  have h3 : 0 ≤ vV T.V (io x) := by
    rw [ho.2 x]
    exact mul_nonneg (Int.natCast_nonneg e) (by unfold vLa; omega)
  refine IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) ?_
  refine (WithZero.log_le_log h1 one_ne_zero).1 ?_
  rw [WithZero.log_one]
  unfold vV at h3
  omega

theorem exists_lift {T : CDVR} {R : Type} [CommRing R] (f : R →+* T.Fr)
    (h : ∀ x, f x ∈ Set.range (algebraMap T.V T.Fr)) : ∃ g : R →+* T.V, ∀ x, algebraMap T.V T.Fr (g x) = f x := by
  choose g hg using h
  have hi : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  exact ⟨{ toFun := g
           map_one' := hi (by simp [hg])
           map_mul' := fun x y => hi (by simp [hg])
           map_zero' := hi (by simp [hg])
           map_add' := fun x y => hi (by simp [hg]) }, hg⟩

theorem vLa_natCast (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (hN : N ≠ 0) :
    vLa la (N : K) = vla la (Ideal.span {(N : 𝓞 K)}) := by
  classical
  have h : (N : K) = algebraMap (𝓞 K) K (N : 𝓞 K) := by simp
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ (by exact_mod_cast hN), WithZero.log_exp, neg_neg, vla]

theorem bound_of_mul_mem {T : CDVR} {N x : T.Fr} (hN : N ≠ 0) (h : N * x ∈ Set.range (algebraMap T.V T.Fr))
    {m : ℤ} (hm : vV T.V N ≤ m) : x = 0 ∨ -m ≤ vV T.V x := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  obtain ⟨v, hv⟩ := h
  have h0 : algebraMap T.V T.Fr v ≠ 0 := hv ▸ mul_ne_zero hN hx
  have h1 : valV T.V (algebraMap T.V T.Fr v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  have h3 : 0 ≤ vV T.V (N * x) := by
    rw [← hv]
    unfold vV
    omega
  rw [vV_mul hN hx] at h3
  omega

theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  have := la.isMaximal
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  letI := Ideal.Quotient.field la.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ la.asIdeal) (ringChar _))

theorem exists_locGen (p : HeightOneSpectrum (𝓞 K)) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    ∃ x : K, IsLocGen p x I ∧ vLa p x = FractionalIdeal.count K p I := by
  obtain ⟨x, hx⟩ := p.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K p I))
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have h1 : ordAt p x = FractionalIdeal.count K p I := by
    rw [ordAt, hx, WithZero.log_exp, neg_neg]
  exact ⟨x, ⟨h0, by rw [← ordAt_eq_count p h0, h1]⟩, h1⟩

end Val

end GlobalTheory.ArcCM.FinLoc

namespace GlobalTheory.ArcCM


open FinLoc in
theorem finLocalAt_of_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.ArcQ.FinLocalAt d w n (-FractionalIdeal.count K₁ w s.Tl.I) (fun τ k => -FractionalIdeal.count K₁ w (s.line τ k).I) (w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la) (intAt Xo c a' n la) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS la w hw a' n
  obtain ⟨Tv, io, hfin, how⟩ := (exists_finSite_norm_eq_zpow_siteAlg K₁ w).1
  have hvw : ∀ x : K₁, vV Tv.V (io x) = vLa w x := fun x => by rw [how.2 x]; simp
  have hlo : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 c.F) := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]
    exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot)
  have hola : OverLa la Tv.V (io.comp (algebraMap c.F K₁)) (w.asIdeal.ramificationIdx (𝓞 c.F)) :=
    ⟨he, fun x => (hvw _).trans (ordAt_algebraMap_of_liesOver hw x)⟩

  obtain ⟨p, hp, hpl⟩ := exists_prime_mem la
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  obtain ⟨Wl, hpW, hWl⟩ := exists_valuationSubring_complex_comap_val_eq c.F _ p hpU
  obtain ⟨Yw, h4, hpush⟩ := hM p Wl hp hpW
  obtain ⟨b, hb⟩ := exists_lift (T := Tv) ((io.comp (algebraMap c.F K₁)).comp (c.V Wl).subtype) fun x =>
    mem_range_of_le_one hola (by
      have hx : (x : c.F) ∈ Wl.comap c.F.val.toRingHom := x.2
      rw [hWl] at hx
      exact hx)
  obtain ⟨ρ, hρ⟩ := exists_lift (T := Tv) (io.comp (algebraMap (𝓞 K₁) K₁)) fun x =>
    mem_range_of_le_one how (w.valuation_le_one x)
  have hρ' : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁) := hρ

  obtain ⟨aw, aK, pw, pK, ψ, bw, bK, hψ, hsq, htau⟩ :=
    GlobalTheory.ArcCM.exists_arcIn_over_valuationRing hK E H Dw l c K₁ d.a d.e d.th d.jj n' La c₁ s Tv io ρ _ (c.V Wl).subtype b hρ' hb
  obtain ⟨M, m₁, m₂, m₃, m₄, m₅, hγ, hg, hbas⟩ := exists_intModel_heq hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c K₁ d
    Tv io Wl Yw b aw aK pw pK h4 (arcDatum_arcLieBasis hK.laws hK.laws2 E H Dw l Xo c K₁ d s.tan) bw bK
  subst m₁
  obtain rfl := eq_of_heq m₂
  subst m₃
  obtain rfl := eq_of_heq m₄
  obtain rfl := eq_of_heq m₅

  have hn' : n' ≠ 0 := s.n_pos.ne'
  have hm : ∀ N : ℕ, N ≠ 0 → vla la (Ideal.span {(N : 𝓞 c.F)}) ≤ mOf E n' la →
      vV Tv.V (N : Tv.Fr) ≤ ((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) := fun N hN h => by
    have e := hola.2 (N : c.F)
    rw [map_natCast, vLa_natCast la hN] at e
    rw [e]
    exact_mod_cast Nat.mul_le_mul_left _ h
  have key : ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), ∃ cl : K₁, cl ≠ 0 ∧
      vLa w cl = FractionalIdeal.count K₁ w (s.line τ k).I ∧ ∀ j, io cl * M.g τ k j = 0 ∨
        -((w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la : ℕ) : ℤ) ≤ vV Tv.V (io cl * M.g τ k j) := by
    intro τ k
    cases hk : s.kind τ k with
    | none =>
      have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
      refine ⟨1, one_ne_zero, ?_, fun j => ?_⟩
      · simp [CMIn.line, hk, MLine.one, vLa, FractionalIdeal.count_one]
      · have h := GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _
          (GlobalTheory.XiIntegral.discr_mul_xi_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k hk) j
        refine bound_of_mul_mem (N := ((NumberField.discr E).natAbs : Tv.Fr)) (by exact_mod_cast hd) ?_
          (hm _ hd (le_max_left _ _))
        rw [map_one, _root_.one_mul]
        obtain ⟨v, hv⟩ := h
        rcases Int.natAbs_eq (NumberField.discr E) with h' | h'
        · exact ⟨v, by rw [hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_natCast]⟩
        · exact ⟨-v, by rw [map_neg, hv, congrArg (Int.cast : ℤ → Tv.Fr) h', Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg]⟩
    | some m =>
      obtain ⟨cl, hcl, hv⟩ := exists_locGen w (s.line τ k).I
      refine ⟨cl, hcl.1, hv, fun j => ?_⟩
      have h := GlobalTheory.IntLetterCoord.main hK E H Dw l Xo c K₁ d Tv io Wl M Yw h4 hbas τ k _
        (GlobalTheory.ArcCM.abelian_letter_integral hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau τ k m cl hk hcl) j
      refine bound_of_mul_mem (N := (n' : Tv.Fr)) (by exact_mod_cast hn') ?_ (hm _ hn' (le_max_right _ _))
      rwa [map_mul, map_natCast, _root_.mul_assoc] at h
  choose cl hcl₀ hcl₁ hcl₂ using key
  have hio : ∀ τ k, io (cl τ k) ≠ 0 := fun τ k => (map_ne_zero io).2 (hcl₀ τ k)
  refine GlobalTheory.ArcQ.finLocalAt_of_intModel hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d w Tv io Wl Yw M la _
    (fun τ k => (io (cl τ k))⁻¹) (fun τ => Matrix.diagonal (fun k => io (cl τ k)) * M.g τ) _ _ _ hS.1 hfin how hola h4
    hpush hbas ⟨hγ, GlobalTheory.ArcGamma.vV_gamma hK E H Dw l Xo c K₁ d n' La c₁ s w Tv io Wl M ρ ψ how hρ' hψ hsq htau hγ⟩
    (fun τ k => ⟨inv_ne_zero (hio τ k), ?_⟩) (fun τ => ?_) (fun τ k j => ?_) (fun τ k j => ?_) a' n
  · rw [← hcl₁, ← hvw]
    simp [vV]
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hio τ k) (hg τ)
  · rw [Matrix.diagonal_mul, inv_mul_cancel_left₀ (hio τ k)]
  · rw [Matrix.diagonal_mul]
    exact hcl₂ τ k j

end GlobalTheory.ArcCM
end

