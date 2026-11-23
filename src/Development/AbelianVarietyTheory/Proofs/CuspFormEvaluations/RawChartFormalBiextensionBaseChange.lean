module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsFrameRawChartBaseChange
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartBaseChangeRigGerm

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RawChartBaseChange

theorem isCanonGauge_mapFB {S S' : Type} [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S']
    (ψ : S →+* S') {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB S d O)
    (h : Germ.PS S 2 d) (hh : B.IsCanonGauge S h) :
    (FBMap.mapFB ψ B).IsCanonGauge S' (MvPowerSeries.map ψ h) := by
  letI : Algebra S S' := ψ.toAlgebra
  have H : B.IsCanonGauge S' (MvPowerSeries.map ψ h) :=
    GaugeBaseChange.isCanonGauge_map B (Algebra.ofId S S') hh
  have hK : ∀ {n : ℕ} (f : Germ.PS S n d),
      Germ.FB.toK S' (MvPowerSeries.map ψ f : Germ.PS S' n d) = Germ.FB.toK S' f := by
    intro n f
    ext m
    rfl
  have hF : (FBMap.mapFB ψ B).FK S' = B.FK S' := funext fun i => hK (B.G.F i)
  have hA : ∀ a, (FBMap.mapFB ψ B).actK S' a = B.actK S' a :=
    fun a => funext fun i => hK (B.A.act a i)
  refine ⟨H.ax0, H.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK B.ph1).trans H.ph1
  · rw [hF]; exact (hK B.ph2).trans H.ph2
  · exact (hK B.sy).trans H.sy
  · rw [hA, hA]; exact (hK (B.ad a)).trans (H.ad a)

end GlobalTheory.RawChartBaseChange

namespace GlobalTheory

theorem rawChart_baseChange : RawBCSt := by
  intro E _ _ _ H Dw l Xo c _ S S' _ _ _ _ _ _ ψ x0 u C
  obtain ⟨e', hg, hc, -⟩ := _root_.GlobalTheory.RawFrameBC.exists_frames E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
    (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) C.e C.frame.gen
  have hG := _root_.GlobalTheory.rawChart_baseChange_rig_germ E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
    (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) C.e e' C.frame.gen hg hc
    C.wP C.prim.1
  refine ⟨FBMap.mapFB (ψ : S →+* S') C.B, fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m, e',
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ?_,
    RawChartBaseChange.isCanonGauge_mapFB _ C.B C.h C.gauge, hG.1 C.rig0, hG.2⟩
  · exact _root_.GlobalTheory.RawChartBC.rIsChart_baseChange E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
      (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) u C.uvec C.chart
  · exact _root_.GlobalTheory.isFrame_baseChange E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
      (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) C.e e' C.frame.gen hg hc
      _ _ _ _ C.frame

end GlobalTheory
