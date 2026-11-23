module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqLoc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointSeries_frames_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  first | exact @GlobalTheory.FrameAdjDown.adjoint_series_pull_back | exact GlobalTheory.FrameAdjDown.adjoint_series_pull_back | (intros; apply GlobalTheory.FrameAdjDown.adjoint_series_pull_back <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.CarryCalc

variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem carries_iff (w : LB.Iso L' (L.pull F)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) :
    Carries L F w φ ε g g' ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
        gm r z (LB.wchart L (fun k => φ k ≫ F) p) (g'.s p) = pw w φ ε r z p q * gm r z (LB.wchart L' φ q) (g.s q) := by
  refine (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g')
    (fun j x hx => wchart_pull_le L F φ j hx) (fun j => rfl)).trans ⟨fun H Z r z p q hp hq => ?_, fun H Z r z p q hp hq => ?_⟩
  · have := H Z r z p q (Set.mem_iInter.1 hp) (Set.mem_iInter.1 hq)
    rw [Category.comp_id] at this
    exact this
  · rw [Category.comp_id]
    exact H Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

def fac (w : LB.Iso L' (L.pull F)) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

theorem val_of_carries {w : LB.Iso L' (L.pull F)} {φ : K → (Y ⟶ X')} {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)}
    {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (H : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, fac w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine ((carries_iff w φ ε g g').1 H Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [pw, fac, Category.assoc]

theorem carries_of_val {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {φ : K → (Y ⟶ X')}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (hg : g.IsGen)
    (hg' : g'.IsGen) (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val g' (𝟙 Y) y J = (∏ k, fac w y J J' (𝟙 Y ≫ φ k) ^ ε k) * val g (𝟙 Y) y J') : Carries L F w φ ε g g' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
  have hc := (carries_iff w φ ε g t).2 hv
  have e : ∀ j, g'.s j = t.s j := fun j => unit_ext fun y hy => by
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    choose J' hJ' using fun ψ : Y ⟶ X' => exists_chart hL' (ψ y)
    have v' : val g' (𝟙 Y) y J = val t (𝟙 Y) y J := (h y J J' hJ hJ').trans (val_of_carries hc (𝟙 Y) hJ hJ').symm
    exact (gen_trans hg' (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).trans ((congrArg _ v').trans
      (gen_trans ht (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).symm)
  obtain ⟨s⟩ := g'
  obtain ⟨s'⟩ := t
  obtain rfl : s = s' := funext e
  exact hc

theorem exists_good' {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hM (ψ z)
  exact ⟨J, hJ⟩

end GlobalTheory.ChartCmp.CarryCalc

namespace GlobalTheory.ChartCmp
open CarryCalc

theorem carries_calculus : ∀ (X X' : Scheme.{0}) (L' : LB X') (L : LB X) (F : X' ⟶ X) [Mono F] (w : LB.Iso L' (L.pull F)), L'.IsLB → L.IsLB → w.IsGen → (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)), g.IsGen → ∃ g', g'.IsGen ∧ Carries L F w φ ε g g') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h', LB.SameSum φ ε φ' ε' → g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → (LB.Gen.Corr L' _ _ _ _ g h ↔ LB.Gen.Corr L _ _ _ _ g' h')) ∧ (∀ (Y Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g' (r : Z ⟶ Y) (g'' : LB.Gen (LB.LinComb L (fun k => (r ≫ φ k) ≫ F) ε)), g.IsGen → g'.IsGen → g''.IsGen → Carries L F w φ ε g g' → LB.Gen.Corr L _ _ _ _ g'' (LB.pullGen L _ _ g' r) → Carries L F w (fun k => r ≫ φ k) ε (LB.pullGen L' φ ε g r) g'') ∧ (∀ (Y : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) (h : LB.Gen (LB.LinComb L' φ' ε')) g' h' (p : LB.Gen (LB.LinComb L (fun k => Sum.elim φ φ' k ≫ F) (Sum.elim ε ε'))), g.IsGen → h.IsGen → g'.IsGen → h'.IsGen → p.IsGen → Carries L F w φ ε g g' → Carries L F w φ' ε' h h' → LB.Gen.Corr L _ _ _ _ p (LB.mulGen L _ _ _ _ g' h') → Carries L F w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L' _ _ _ _ g h) p) ∧ (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε)) g', Carries L F w φ ε g g' → Carries L F w φ (fun k => - ε k) (LB.invGen L' φ ε g) (LB.invGen L _ ε g')) := by
  intro X X' L' L F _ w hL' hL hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y K _ φ ε g hg
    obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
    exact ⟨t, ht, (carries_iff w φ ε g t).2 hv⟩
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' hs _ _ _ _ Hg Hh
    have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
        (val g (𝟙 Y) y J' = val h (𝟙 Y) y J' ↔ val g' (𝟙 Y) y J = val h' (𝟙 Y) y J) := fun y J J' hJ hJ' => by
      rw [val_of_carries Hg (𝟙 Y) hJ hJ', val_of_carries Hh (𝟙 Y) hJ hJ',
        DVR.prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => fac w y J J' (𝟙 Y ≫ ψ)), mul_right_inj]
    refine ⟨fun C => corr_of_val hL fun y J hJ => ?_, fun C => corr_of_val hL' fun y J' hJ' => ?_⟩
    · obtain ⟨J', hJ'⟩ := exists_good' hL' y
      exact (key y J J' hJ hJ').1 (val_corr hJ' C _)
    · obtain ⟨J, hJ⟩ := exists_good' hL y
      exact (key y J J' hJ hJ').2 (val_corr hJ C _)
  · intro Y Z K _ φ ε g g' r g'' hg _ hg'' H C
    refine carries_of_val hL' hL hw (DVR.pullGen_isGen _ _ _ _ hg r) hg'' fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_pull hJ, val_pull hJ', val_of_carries H _ hJ hJ']
    simp only [Category.assoc]
  · intro Y K K' _ _ φ ε φ' ε' g h g' h' p hg hh _ _ hp Hg Hh C
    refine carries_of_val hL' hL hw (DVR.mulGen_isGen _ _ _ _ _ _ _ hg hh) hp fun y J J' hJ hJ' => ?_
    rw [val_corr hJ C, val_mul hJ, val_mul hJ', val_of_carries Hg _ hJ hJ', val_of_carries Hh _ hJ hJ',
      Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
    rfl
  · intro Y K _ φ ε g g' H
    refine (carries_iff w φ _ _ _).2 fun Z r z p q hp hq => ?_
    refine (map_inv _ _).trans ((congrArg (·⁻¹) ((carries_iff w φ ε g g').1 H Z r z p q hp hq)).trans ?_)
    refine (mul_inv _ _).trans (congrArg₂ (· * ·) ?_ (map_inv _ _).symm)
    simp only [pw, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.ChartCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V] {d : ℕ}

theorem ev_one_eq {n : ℕ} (a : Pt V n d) (f : PS V 1 d) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin d => a p.2) f := by
  unfold ev
  congr 1
  funext p
  rw [Matrix.cons_val_fin_one]

theorem cc_ev {k n : ℕ} (a : Fin k → Pt V n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS V k d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem cc_comp1 {n : ℕ} {φ : Pt V 1 d} {a : Pt V n d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin d) : MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by rw [Matrix.cons_val_fin_one]; exact ha i) _ (hφ i)

theorem germCompOne_assoc_of_constantCoeff_zero {n : ℕ} (ψ φ : Pt V 1 d) (a : Pt V n d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : comp1 (comp1 ψ φ) a = comp1 ψ (comp1 φ a) := by
  funext i
  simp only [comp1, ev_one_eq]
  exact MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => hφ p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem germCompOne_identityPoint_left {n : ℕ} (a : Pt V n d) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    comp1 (pt V (n := 1) d 0) a = a := by
  funext i
  simp only [comp1, ev_one_eq, pt]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin d => ha p.2) _

theorem eq_comp1_inv {n : ℕ} {φ φi : Pt V 1 d} (h : IsInvPair φ φi) {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : comp1 φ a = b) : a = comp1 φi b := by
  rw [← e, ← germCompOne_assoc_of_constantCoeff_zero φi φ a h.1 ha, h.2.2.2, germCompOne_identityPoint_left a ha]

def sub (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m k :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin k × Fin d => a p.1 p.2)

def sub1 (m : ℕ) {n : ℕ} (a : Pt V n d) : jOG (𝟙 (Sp V)) d m n ⟶ jOG (𝟙 (Sp V)) d m 1 :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d => a p.2)

theorem hom_comp (m : ℕ) {κ κ' κ'' : Type} [Fintype κ'] [DecidableEq κ'] [Fintype κ''] [DecidableEq κ'']
    (g : κ → MvPowerSeries κ' V) (h : κ' → MvPowerSeries κ'' V) (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) h) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) g) =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun i => MvPowerSeries.subst h (g i)) := by
  rw [GermD.homAt_comp]
  congr 1
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m g hg, ExpChartJet.jetSubstPS_psJet m h hh,
    ExpChartJet.jetSubstPS_mk m _ (fun i => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hh) hh (hg i))]

theorem jetSchemeMap_pointFamily_comp_singlePoint (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) (b : Pt V k d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    sub m a ≫ sub1 m b = sub1 m (fun i => ev a (b i)) :=
  hom_comp m _ _ (fun p => hb p.2) (fun p => ha p.1 p.2)

theorem jetSchemeMap_singlePoint_comp_singlePoint (m : ℕ) {n : ℕ} (a : Pt V n d) (φ : Pt V 1 d)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    sub1 m a ≫ sub1 m φ = sub1 m (comp1 φ a) := by
  have e : sub1 m (comp1 φ a) = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) fun p : Fin 1 × Fin d =>
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => a q.2) (φ p.2)) := by
    simp only [sub1, comp1, ev_one_eq]
  rw [e]
  exact hom_comp m _ _ (fun p => hφ p.2) (fun p => ha p.2)

theorem eq_of_jetSchemeMap_singlePoint_universal {G : Over (Sp V)} [GrpObj G] {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {n : ℕ} {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (h : ∀ m, sub1 m a ≫ x m = sub1 m b ≫ x m) : a = b := by
  funext i
  refine GermFun.psJet_inj fun m => ?_
  have hk : RingHom.ker (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ^ (m + 1) = ⊥ := by
    have ea : (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) = Chart.jetAug V _ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow _ m
  have aa := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2)
  have ab := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)
  have h1 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ≫ (sub1 m a ≫ x m) = 1 := by
    rw [sub1, ← Category.assoc, GermD.homAt_comp, aa]
    exact hx.2.1 m
  have e := (hx.2.2 _ jetAug m hk _ h1).unique ⟨aa, rfl⟩ ⟨ab, h m⟩
  have e' := AlgHom.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2),
    ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)] at e'

theorem jptG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp V))
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (m : ℕ) {n : ℕ} (i : Fin n) :
    jptG t (𝟙 (Sp V)) d x m i = sub1 m (pt V d i) ≫ x m := by
  have e : jetCopy (S := V) d m i = jetSubstPS (m := m) (fun p : Fin 1 × Fin d => pt V d i p.2) := by
    apply GermD.jet_hom_ext
    intro p
    rw [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => pt V d i p.2) (fun _ => MvPowerSeries.constantCoeff_X _),
      jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X, pt, ← MvPolynomial.coe_X]
    rw [psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rw [jptG, e]
  rfl

end GlobalTheory.ChartCmp.CoordLaw


open GlobalTheory.ChartCmp.CoordLaw in
theorem GlobalTheory.ChartCmp.law_act_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ φi hc hc' hu hinv hrel
  have hφ := hinv.1
  have hr : ∀ m, x' m = sub1 m φ ≫ x m := hrel
  have hpt : ∀ (j : Fin 2) i, MvPowerSeries.constantCoeff (pt V d j i) = 0 := fun j i => MvPowerSeries.constantCoeff_X _
  refine ⟨?_, fun a => ?_⟩
  · let A : Fin 2 → Pt V 2 d := ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)]
    have hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0 := by
      intro j i
      fin_cases j <;> exact cc_comp1 hφ (hpt _) i
    have hX : ∀ j, (fun i => ev A (pt V d j i)) = A j := fun j => funext fun i =>
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 2 × Fin d => hA p.1 p.2) (j, i)
    have key : comp1 φ B'.G.F = addOf B.G.F (comp1 φ (pt V (n := 2) d 0)) (comp1 φ (pt V (n := 2) d 1)) := by
      refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ B'.G.const) (fun i => cc_ev A hA _ (B.G.const i)) fun m => ?_
      have l : sub1 m B.G.F ≫ x m = _ := hc.law m
      have l' : sub1 m B'.G.F ≫ x' m = _ := hc'.law m
      have l2 := congrArg (fun f => sub m A ≫ f) l
      simp only [jptG_eq, MonObj.comp_mul, ← Category.assoc, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA B.G.const, jetSchemeMap_pointFamily_comp_singlePoint m A _ hA (hpt _),
        hX] at l2
      simp only [jptG_eq, hr m, ← Category.assoc, jetSchemeMap_singlePoint_comp_singlePoint m _ φ B'.G.const hφ, jetSchemeMap_singlePoint_comp_singlePoint m _ φ (hpt _) hφ] at l'
      exact l'.trans l2.symm
    exact fun i => congrFun (eq_comp1_inv hinv B'.G.const key) i
  · refine eq_comp1_inv hinv (B'.A.const a) ?_
    refine eq_of_jetSchemeMap_singlePoint_universal hu (cc_comp1 hφ (B'.A.const a)) (cc_comp1 (B.A.const a) hφ) fun m => ?_
    have l : x m ≫ t.act.act a = sub1 m (B.A.act a) ≫ x m := hc.act m a
    have l' : x' m ≫ t.act.act a = sub1 m (B'.A.act a) ≫ x' m := hc'.act m a
    rw [← jetSchemeMap_singlePoint_comp_singlePoint m _ φ (B'.A.const a) hφ, ← jetSchemeMap_singlePoint_comp_singlePoint m φ _ hφ (B.A.const a), Category.assoc, Category.assoc, ← hr m,
      ← l', ← l, hr m, Category.assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffInvariantPolyOperatorJetEq
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem constantCoeff_DpolyN_jEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  intro k _ d n F Ix _ cp u P m f g hP hfg
  classical
  rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P f _ subset_rfl,
    GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P g _ subset_rfl]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  refine GlobalTheory.PowGerm.NabJet.constantCoeff_DmonN_congr F cp u e f g fun mo hmo => ?_
  refine hfg mo (hmo.trans (le_trans ?_ hP))
  have := MvPolynomial.le_totalDegree he
  rwa [Finsupp.degree_apply]

end GlobalTheory.ChartCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCoordinateRelationUniversalJets
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V]

theorem uniq {G : Over (Sp V)} [GrpObj G] {κ : Type} {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A : Type} [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    {ψ₁ ψ₂ : Jet V κ m →ₐ[V] A} (h1 : aug.comp ψ₁ = jetAug) (h2 : aug.comp ψ₂ = jetAug)
    (e : Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₂ ≫ x m) : ψ₁ = ψ₂ := by
  have hy : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m) = 1 := by
    rw [← Category.assoc, GermD.homAt_comp, h1, hx.2.1]
  exact (hx.2.2 A aug m hk _ hy).unique ⟨h1, rfl⟩ ⟨h2, e⟩

theorem jetSubstP_trunc {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (φ : κ → MvPowerSeries κ' V) :
    jetSubstP m (fun p => psTrunc m (φ p)) = jetSubstPS (m := m) φ := rfl

theorem aug_X {κ : Type} (m : ℕ) (j : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = 0 := ExpUniqJet.augmentation_jet_variable m j

theorem aug_comp_subst {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (m : ℕ)
    (φ : κ → MvPowerSeries κ' V) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    (jetAug : Jet V κ' m →ₐ[V] V).comp (jetSubstPS (m := m) φ) = jetAug := by
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ hφ, GaugeR.jetAug_psJet, hφ, aug_X]

theorem exists_coord {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    (hx' : GlobalTheory.PowGerm.IsUnivJ G κ' x') :
    ∃ φ : κ → MvPowerSeries κ' V, (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
      ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m := by
  have h := fun m => (hx.2.2 (Jet V κ' m) jetAug m (ExpUniqLoc.ker_aug_pow le_rfl) (x' m) (hx'.2.1 m)).exists
  choose ψ hψa hψ using h
  have hc : ∀ m, (jetTrunc : Jet V κ' (m + 1) →ₐ[V] Jet V κ' m).comp (ψ (m + 1)) =
      (ψ m).comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) := by
    intro m
    refine uniq hx (jetAug : Jet V κ' m →ₐ[V] V) (m + 1) (ExpUniqLoc.ker_aug_pow (by omega)) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, ExpUniqLoc.aug_comp_trunc, hψa]
    · rw [← AlgHom.comp_assoc, hψa, ExpUniqLoc.aug_comp_trunc]
    · rw [← GermD.homAt_comp, ← GermD.homAt_comp, Category.assoc, Category.assoc, hx.1, ← hψ, ← hψ, hx'.1]
  have hs := fun i : κ => GaugeR.exists_ps_of_compat
    (fun m => ψ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) (fun m => DFunLike.congr_fun (hc m) _)
  choose φ hφ using hs
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := by
    intro i
    rw [← GaugeR.jetAug_psJet 0, hφ, ← AlgHom.comp_apply, hψa, aug_X]
  refine ⟨φ, h0, fun m => ?_⟩
  have : jetSubstPS (m := m) φ = ψ m := by
    apply GermD.jet_hom_ext
    intro i
    rw [ExpChartJet.jetSubstPS_mk m φ h0, hφ]
  rw [this]
  exact hψ m

theorem subst_eq_X {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    {φ : κ → MvPowerSeries κ' V} (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m)
    {φi : κ' → MvPowerSeries κ V} (h0i : ∀ i, MvPowerSeries.constantCoeff (φi i) = 0)
    (hφi : ∀ m, x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φi) ≫ x' m) (i : κ) :
    MvPowerSeries.subst φi (φ i) = MvPowerSeries.X i := by
  apply GermFun.psJet_inj
  intro m
  have e : (jetSubstPS (m := m) φi).comp (jetSubstPS (m := m) φ) = AlgHom.id V _ := by
    refine uniq hx (jetAug : Jet V κ m →ₐ[V] V) m (ExpUniqLoc.ker_aug_pow le_rfl) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, aug_comp_subst m φi h0i, aug_comp_subst m φ h0]
    · rfl
    · rw [← GermD.homAt_comp, Category.assoc, ← hφ, ← hφi, GermD.homAt_id, Category.id_comp]
  have e' := DFunLike.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ h0, ExpChartJet.jetSubstPS_psJet m φi h0i] at e'
  rw [e', ← MvPolynomial.coe_X]
  exact (GaugeR.psJet_eq_mk m _ _ fun e _ => (MvPolynomial.coeff_coe _ _).symm).symm

end GlobalTheory.ChartCmp.Coord

namespace GlobalTheory.ChartCmp

theorem exists_coordRel_of_isUnivJ : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  intro V _ G _ d x x' hx hx'
  obtain ⟨φ, h0, hφ⟩ := Coord.exists_coord hx hx'
  obtain ⟨φi, h0i, hφi⟩ := Coord.exists_coord hx' hx
  have key : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V, (fun p : Fin 1 × Fin d => f (0, p.2)) = f := by
    intro f
    funext p
    rw [show ((0 : Fin 1), p.2) = p from Prod.ext (Subsingleton.elim _ _) rfl]
  have key2 : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V,
      (fun p : Fin 1 × Fin d => (![fun j => f (0, j)] : Fin 1 → Pt V 1 d) p.1 p.2) = f := by
    intro f
    funext p
    obtain ⟨a, b⟩ := p
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun j => φ (0, j), fun j => φi (0, j), ⟨fun i => h0 _, fun i => h0i _, ?_, ?_⟩, fun m => ?_, fun m => ?_⟩
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx h0 hφ h0i hφi _
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx' h0i hφi h0 hφ _
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φ (0, p.2)), key]
    exact hφ m
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φi (0, p.2)), key]
    exact hφi m

end GlobalTheory.ChartCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCmp

theorem isMonHom_of_mul_points {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have e := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at e
    have e2 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have := e.symm
      exact mul_eq_left.1 this
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _)] using e2
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
      using h (G ⊗ G) (fst G G) (snd G G)

theorem exists_iso_of_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), ∃ ψ : t.G ≅ t'.G, ψ.hom.left = n.φ ∧ IsMonHom ψ.hom ∧ (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) ∧ n.cm.F3 = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ∧ ∃ w : LB.Iso t.PP.L (t'.PP.L.pull n.φ), CubIso n w := by
  intro E _ _ _ H V _ t t' n
  have hp := n.cart.1
  have hw : n.cm.F ≫ t'.G.hom = t.G.hom := by simpa using hp.w
  haveI : IsIso n.cm.F := hp.isIso_fst_of_isIso
  let ψ : t.G ≅ t'.G := Over.isoMk (asIso n.cm.F) hw
  have hψ : ψ.hom.left = n.cm.F := rfl
  refine ⟨ψ, rfl, ?_, fun a => ?_, ?_, ?_⟩
  · refine isMonHom_of_mul_points _ fun T x y => ?_
    apply Over.OverMorphism.ext
    have e := n.cart.2 T x y (pushPt hp.w x) (pushPt hp.w y) rfl rfl
    rw [Over.comp_left, hψ, ← e]
    exact mul_left_congr (Category.comp_id _) _ _ (x ≫ ψ.hom) (y ≫ ψ.hom) rfl rfl
  · apply Over.OverMorphism.ext
    exact n.act a
  · refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, hψ]
  · obtain ⟨w, h1, -, h3⟩ := n.lin
    exact ⟨w, h1, h3⟩

end GlobalTheory.ChartCmp
end

