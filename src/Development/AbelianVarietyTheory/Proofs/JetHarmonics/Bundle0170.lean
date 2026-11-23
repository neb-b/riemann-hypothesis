module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedValuationBoundAlgebraicPoints
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem combBound_of_depth_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P j}
    {ka wL wF : WeightFamilies.Wt D j} {S : WeightAlgebra.Scal B} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (G : GlobalFamilyData X ka wL wF) (c : ℝ) (hc0 : 0 ≤ c)
    (hH1 : ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la + c * X.phiC la y : ℝ) : EReal))
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.CombBound G S c nus := by
  intro la y
  have hφ := Formalism.MainNotions.Gaps.T0.phiC_nonneg X la y
  have hd := hH1 la y
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · obtain ⟨hi, h⟩ := hEt hj
    have hi' : (0 : ℝ) < 2 * (G.iet : ℝ) := by positivity
    have h1 := h la y
    have h0 : (0 : ℝ) ≤ 2 * G.iet * X.phiC la y := mul_nonneg hi'.le hφ
    refine ⟨le_trans (by exact_mod_cast h0) h1, fun hfin => hd.trans ?_⟩
    rw [← EReal.coe_toReal hfin (X.vAt_ne_bot la y _), EReal.coe_le_coe_iff] at h1
    rw [EReal.coe_le_coe_iff]
    have h2 : X.phiC la y ≤ (X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) := by
      rw [le_div_iff₀ hi']; linarith
    have h4 : c * X.phiC la y ≤ c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 hc0
    have h5 : c / (2 * (G.iet : ℝ)) * (X.vAt la y (X.inc _ G.et)).toReal =
        c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) := by ring
    rw [h5]
    linarith
  · have h0 : X.phiC la y = 0 := by
      unfold WeightAlgebra.PJ.phiC
      rw [if_neg (not_lt.2 hj)]
    rw [h0, mul_zero, add_zero] at hd
    exact hd

theorem combBound_alg : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (ka wF : WeightFamilies.Wt D j) (S : WeightAlgebra.Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka w wF), S.sW = sWt (recB h.toLawsCore) hinj EX w → (j < D.R.m → 0 < G.iet ∧ EtVal h j hj G.iet G.et) → CombBound G S c (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  intro hH D T h j hj hinj EX w c hO hR ka wF S G hS hEt
  refine combBound_of_depth_le G c hR.2.2.2.1 (fun la y => ?_) hEt
  rw [hS]
  exact _root_.GlobalTheory.RecDepth.depth_le hH D T h j hj hinj EX w c hO hR la y

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepth2Run
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth2_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepth2 N O := by
  intro hAv hHT D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (lR Tp hK j).n := by
    intro j _
    show _ ≤ Tp.nWn
    refine le_trans ?_ Tp.nW_lo.1
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  have hL : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun hM EX _ _ _ _ _ hn
  refine GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι N (numOf D L)
    hR.E_eq hR.σ_eq hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hL.piSplit hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ?_
  intro la hla j
  obtain ⟨Ap, hAp0, hAp, hle⟩ := _root_.GlobalTheory.RunDepth.sizes_bound_two D L Pm Tp hK T.Q hM.pins hx hb O.C hPg.1 (ι j) (hR.inR j)
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨hsp, h2, hvd, hup⟩ := _root_.GlobalTheory.CharDepth.twoPlaces_host D T.Q.H hM.pins.1.1 (resCharOf la) (hR.sm_eq ▸ hla)
  refine ⟨_, ?_, _root_.GlobalTheory.CharDepth.nuW_le_two (resCharOf la) (hAv _) (hHT _) D.host.E T.Q.H (T.Q.Dw (ι j)) T.Q.l (T.Q.Xo (ι j)) T.Q.c
    hR.star_eq D.R.f (D.host.vdH (resCharOf la)) hvd hsp h2 la rfl _ _ _ (fun τ _ _ h => (hL.wts _ (hR.inR j)).1 τ h)
    (DepthTie.card_of_laws T _ hL hM.pins (ι j) (hR.inR j)) Ap hAp0 hAp⟩
  unfold OnObj.sC OnObj.Se
  rw [hR.T_eq, hR.m_eq, hR.vd_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (Nat.cast_nonneg _)) hle
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hAp0
end

