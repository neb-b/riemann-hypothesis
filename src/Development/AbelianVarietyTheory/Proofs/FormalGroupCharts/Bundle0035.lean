module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPush
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalBiextensionsRelatedOfTripleMapOverId
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jrel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t t' n hs d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨y, hy, hyu, hyc, hycomb⟩ := _root_.GlobalTheory.PushChart.pushChart E H V t t' n d x
  obtain ⟨_, _, _, _, _, w, hw⟩ := _root_.GlobalTheory.ChartCmp.exists_iso_of_sabMap_id E H V t t' n
  obtain ⟨hg, h1, h2, h3, h4⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨f, hp⟩ := _root_.GlobalTheory.ChartCmp.exists_pushFr E H V t t' n w d x y e hw.1 hy hg
  have hfy : IsFrameG t' (𝟙 (Sp V)) d y B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad f :=
    (isFrameG_iff t' _ d y _ _ _ _ _ _ f).2
      ⟨fun m => (hp m).1,
        _root_.GlobalTheory.famPh1_push E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h1,
        _root_.GlobalTheory.PushSecondLaw.famPh2_push E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h2,
        _root_.GlobalTheory.PushSym.famSy_push E H V t t' n w d x y e f hw hy hg hp _ h3,
        _root_.GlobalTheory.ChartCmp.PushAd.famAd_push E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h4⟩
  obtain ⟨φ, φi, hj, hd⟩ := _root_.GlobalTheory.ChartCmp.jRel_of_charts_frames E H hstar V t' hs d B B' κ κ' (fun l => tg l ≫ n.φ) tg' uv uv' y x' f e'
    (hyc _ _ κ tg uv hc) hc' (hyu hu) hu' hfy hf'
  exact ⟨φ, φi, hj, fun u u' v h h' => hd u u' _ (hycomb u v h) h'⟩

end GlobalTheory.ChartCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartsCompleteDvr
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.intChart : IntChartStatement :=
  intChart_of_cut
    (fun E _ _ _ H X0 t S _ _ x0 κ _ tg h1 h2 =>
      GlobalTheory.ChartData.exists_isChartG_of_basis E H X0 t S x0 κ tg h1 h2)
    (fun E _ _ _ H X0 t S _ _ x0 d G A κ _ tg uvec x h => _root_.GlobalTheory.exists_frames_of_chart E H X0 t S x0 d G A κ tg uvec x h)
    GlobalTheory.FrameBiextId.fbId GlobalTheory.globalFns_holds
end
end

