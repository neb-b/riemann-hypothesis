module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameAdjDown

section General

variable {X0 X' Y Z A A' : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K K₂ : Type} [Fintype K] [Fintype K₂]

def scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X0) → L.ι} (hJ : Good L z J) : val (scl u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem pmaps_of_flat (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) :
    PMaps w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h
  refine unit_ext fun y hy => ?_
  have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
  have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
    wchart_pull_le L F φ' j hy
  refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
  refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
  have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
  rw [Category.comp_id] at e
  exact e.symm

theorem corr_down (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    {ψ : K → (A ⟶ X0)} {ψ' : K → (A' ⟶ X')} {ε : K → ℤ} {U : A' ⟶ A} (hψ : ∀ k, ψ' k ≫ F = U ≫ ψ k)
    {g : LB.Gen (LB.LinComb L ψ ε)} {g' : LB.Gen (LB.LinComb L' ψ' ε)} (hg : PMaps w ψ' ψ ε g' g U)
    {φ : K₂ → (Y ⟶ X0)} {φ' : K₂ → (Y ⟶ X')} {δ : K₂ → ℤ} {e : LB.Gen (LB.LinComb L φ δ)}
    {e' : LB.Gen (LB.LinComb L' φ' δ)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) δ)}
    (hc : LB.Gen.Corr L _ _ _ _ c e) (hm : LB.Gen.Maps (LB.linCombIso w φ' δ) e' (flatGen L F φ' δ c))
    {l : Y ⟶ A} {l' : Y ⟶ A'} (hl : l' ≫ U = l) (σ₁ σ₂ : Y ⟶ Y) (u : Γ(Y, ⊤)ˣ)
    (hF : ∀ (V : Type) [CommGroup V] (h : (Y ⟶ X') → V),
      (∏ k, h (l' ≫ ψ' k) ^ ε k) * ∏ k, h (σ₁ ≫ φ' k) ^ δ k = ∏ k, h (σ₂ ≫ φ' k) ^ δ k)
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ g l) (LB.pullGen L _ _ e σ₁))
      (scl u (LB.pullGen L _ _ e σ₂))) :
    LB.Gen.Corr L' _ _ _ _ (LB.mulGen L' _ _ _ _ (LB.pullGen L' _ _ g' l') (LB.pullGen L' _ _ e' σ₁))
      (scl u (LB.pullGen L' _ _ e' σ₂)) := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have h0 := val_corr hJ H (𝟙 Y)
  rw [val_mul hJ, val_scl _ _ _ hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
    Category.id_comp] at h0
  rw [val_mul hJ', val_scl _ _ _ hJ', val_pull hJ', val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp,
    Category.id_comp]
  have he : ∀ σ : Y ⟶ Y, val e σ y J =
      (∏ k, gw w (σ ≫ φ' k) y (J ((σ ≫ φ' k) ≫ F)) (J' (σ ≫ φ' k)) ^ δ k) * val e' σ y J' := fun σ => by
    have := DegPull.pmaps_val (fun k => (Category.id_comp _).symm) (pmaps_of_flat w φ' δ e' c hm) σ y hJ hJ'
    rw [Category.comp_id] at this
    exact (val_corr hJ hc σ).symm.trans this
  have h1 := DegPull.pmaps_val hψ hg l' y hJ hJ'
  rw [hl] at h1
  have h2 := hF _ (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [h1, he, he, ← h2, _root_.mul_mul_mul_comm, mul_left_comm (gm (𝟙 Y) y ⊤ u)] at h0
  exact mul_left_cancel h0

end General

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameAdjSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_act' {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS S 1 d}
    (h : ∀ m (b : 𝓞 E), x m ≫ t.act.act b =
      homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m)
    (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← homAt_comp, Category.assoc, ← h m a, ← Category.assoc, ren_one]
  try rfl

theorem push_act {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) {T : Over S'}
    (p : T ⟶ t'.G) (a : 𝓞 E) : pushPt mp.cart.1.w (p ≫ t'.act.act a) = pushPt mp.cart.1.w p ≫ t.act.act a :=
  Over.OverMorphism.ext (by
    show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
    rw [Category.assoc, mp.act, Category.assoc])

def sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) :
    Over.mk ((t'.G ⊗ t'.G).hom ≫ f) ⟶ t.G ⊗ t.G :=
  lift (pushPt mp.cart.1.w (fst t'.G t'.G)) (pushPt mp.cart.1.w (snd t'.G t'.G))

theorem adj_comm {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) (a b : 𝓞 E)
    (k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))) :
    Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act b])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G]) k ≫ mp.φ =
      (sqMap mp).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act b])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) k := by
  rcases k with I | I
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · simp [sqMap]
    · exact (push_act mp _ _).trans (by simp [sqMap])
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · exact (push_act mp _ _).trans (by simp [sqMap])
    · simp [sqMap]

theorem lift_sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f)
    {T' : Over S'} {T : Over S} (p' q' : T' ⟶ t'.G) (p q : T ⟶ t.G) (h : T'.left ⟶ T.left)
    (hp : p'.left ≫ mp.φ = h ≫ p.left) (hq : q'.left ≫ mp.φ = h ≫ q.left) :
    (lift p' q').left ≫ (sqMap mp).left = h ≫ (lift p q).left := by
  apply pullback.hom_ext
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (fst t.G t.G).left = (h ≫ (lift p q).left) ≫ (fst t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_fst, lift_fst, ← hp]
    show (lift p' q').left ≫ (fst t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (snd t.G t.G).left = (h ≫ (lift p q).left) ≫ (snd t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_snd, lift_snd, ← hq]
    show (lift p' q').left ≫ (snd t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]


set_option maxHeartbeats 2000000 in
theorem adjoint_series_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e e' _ _ htie act ad a _ hact ⟨wL, hwL, hu⟩
  obtain ⟨wL', hwL', hp⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (sqMap mp).left
    (adj_comm mp a (H.bar a)) wL hwL
  refine ⟨wL', hwL', fun m => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hu m
  obtain ⟨c, hc, hm⟩ := htie m
  refine ⟨u, hu1, ?_⟩
  have hj : ∀ i : Fin 2, (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = 𝟙 _ ≫ (jptG t x0 d x m i).left := fun i => by
    show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
      𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
    rw [Category.assoc, hx, Category.id_comp]
    rfl
  have hl₀ := lift_sqMap mp (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))
    (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2)) (𝟙 (Sp (Jet S (Fin 2 × Fin d) m))) (hj 0) (hj 1)
  have hl : (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left ≫
      (sqMap mp).left = (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left :=
    hl₀.trans (Category.id_comp _)
  refine corr_down (Y := (jOG (𝟙 (Sp S)) d m 2).left) t.PP.isLB t'.PP.isLB w (adj_comm mp a (H.bar a)) hp hc hm hl
    _ _ (unitΓ u) (fun V _ h => ?_) hu2
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act' hact, zpow_neg, Finset.prod_inv_distrib]
  simp only [inv_mul_cancel_right]

end GlobalTheory.FrameAdjDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTriple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameDown

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR

section

variable {X0 X' Y : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K : Type} [Fintype K]

theorem exists_down_val {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q hp hq => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact ((congrArg _ (hs q Z r z p hp hq)).trans (mul_inv_cancel_left _ _)).symm

end

theorem frames_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e he
  have hφ : ∀ m, (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] := by
    intro m
    funext J
    let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
      Over.homMk (𝟙 _) (by simp [overAt])
    have hj : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
      Over.OverMorphism.ext (by
        show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
          𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
        rw [Category.assoc, hx, Category.id_comp]
        rfl)
    refine (psum_push mp.cart _ ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U
      (fun i => ?_) J.down).trans (Category.id_comp _)
    fin_cases i
    · exact hj 0
    · exact hj 1
  choose c₁ hc₁ hcorr using fun m => ChartPrimTrPf.exists_reindex t.PP.L (hφ m) (cε 2) (e m) (he m)
  choose a ha hv using fun m => exists_down_val ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (c₁ m) (hc₁ m)
  exact ⟨a, ha, fun m => ⟨c₁ m, hcorr m, ChartPrimTrPf.maps_flat w _ _ (a m) (c₁ m) (hv m)⟩⟩

end GlobalTheory.FrameDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCubeFramesFromPullbackTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.FrameUp

theorem cube_points_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G)
    (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left) (m : ℕ) :
    cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] =
      fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ := by
  funext J
  let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
    Over.homMk (𝟙 _) (by simp)
  have key : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
    Over.OverMorphism.ext (by
      show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
        𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
      rw [Category.id_comp, Category.assoc, hx]
      rfl)
  refine ((psum_push mp.cart
    ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]
    ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U (fun i => ?_) J.down).trans
      (Category.id_comp _)).symm
  fin_cases i
  · exact key 0
  · exact key 1

theorem exists_frames_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e' he'
  have main : ∀ m, ∃ e : FrTyG t x0 d x m, e.IsGen ∧
      ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ e ∧
        LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
          jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁) := fun m => by
    obtain ⟨c₁, hc₁, hv⟩ := exists_up ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB
      (φ' := cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)])
      (ε := cε 2) (e' m) (he' m)
    have gen : ∀ (ψ : ULift (Finset (Fin 2)) → ((jOG x0 d m 2).left ⟶ t.G.left))
        (c : LB.Gen (LB.LinComb t.PP.L ψ (cε 2))), c.IsGen →
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] = ψ →
        ∃ e : FrTyG t x0 d x m, e.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ c e := by
      intro ψ c hc h
      subst h
      exact ⟨c, hc, ChartPrimTrPf.corr_self _ _ _ c⟩
    obtain ⟨e, he, hce⟩ := gen _ c₁ hc₁ (cube_points_push t x0 t' mp d x x' hx m)
    exact ⟨e, he, c₁, hce, ChartPrimTrPf.maps_flat w _ _ (e' m) c₁ hv⟩
  choose e he hc using main
  exact ⟨e, he, hc⟩

end GlobalTheory.Chart.FrameUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameBCGen

theorem cφG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T T' : Over X0} (ρ : T' ⟶ T) (a b : T ⟶ t.G) :
    cφG t ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφG t ![a, b] I := by
  funext I
  refine Eq.symm (congrArg (fun q => q.left) ((psum_hom (preHom ρ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_))))
  fin_cases i <;> rfl

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t x1 d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx e he
  subst h01
  let ρ : ∀ m, jOG (spMap ψ ≫ x0) d m 2 ⟶ jOG x0 d m 2 := fun m =>
    Over.homMk (spMap (jetCoef ψ (Fin 2 × Fin d) m)) (by
      show spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (algebraMap S (Jet S (Fin 2 × Fin d) m)) ≫ x0 =
        spMap (algebraMap S' (Jet S' (Fin 2 × Fin d) m)) ≫ spMap ψ ≫ x0
      rw [← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq, JetTr.jetCoef_alg])
  have hp : ∀ m (i : Fin 2), jptG t (spMap ψ ≫ x0) d x' m i = ρ m ≫ jptG t x0 d x m i := by
    intro m i
    apply Over.OverMorphism.ext
    show spMap (jetCopy (S := S') d m i).toRingHom ≫ (x' m).left =
      spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (jetCopy (S := S) d m i).toRingHom ≫ (x m).left
    rw [hx, ← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq]
    exact congrArg (fun f => spMap f ≫ (x m).left) (JetTr.jetCoef_copy ψ d m 2 i).symm
  have key := fun m => RawFrameBC.exists_reindexed_pull t.PP.isLB
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (he m) (ρ m).left
    (cφG t ![jptG t (spMap ψ ≫ x0) d x' m (0 : Fin 2), jptG t (spMap ψ ≫ x0) d x' m (1 : Fin 2)])
    (by rw [hp, hp, cφG_comp])
  choose e' h₁ h₂ _ using key
  exact ⟨e', h₁, h₂⟩

end GlobalTheory.FrameBCGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem isAbelianScheme_of_pullback_univ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (X1 : Scheme.{0}) (t' : SAB H X1) (f : X1 ⟶ Xo.X) (mp : SABMap t' Xo.univ.t f), IsAbelianScheme t'.G := by
  intro E _ _ _ H Dw l Xo X1 t' f mp
  have hp : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) mp.cart.1 Xo.univ.proper
  exact ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

section Push

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} {G' : Over (Sp S)}
  [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

def algPtPush (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A] :
    (overAt (𝟙 (Sp S)) A ⟶ G') →* (overAt x0 A ⟶ G) :=
  (preHom (Over.homMk (𝟙 (Sp A)) (by simp) :
    overAt x0 A ⟶ Over.mk ((overAt (𝟙 (Sp S)) A).hom ≫ x0))).comp (pushHom h (overAt (𝟙 (Sp S)) A))

theorem algPtPush_left (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A]
    (a : overAt (𝟙 (Sp S)) A ⟶ G') : (algPtPush h A a).left = a.left ≫ φ :=
  Category.id_comp (a.left ≫ φ)

theorem algPtPush_injective (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A] :
    Function.Injective (algPtPush h A) := fun a b e => by
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w a).trans (Over.w b).symm))
  exact (algPtPush_left h A a).symm.trans ((congrArg (fun q => q.left) e).trans (algPtPush_left h A b))

theorem algPtPush_homAt (h : IsGrpPullback G' G x0 φ) {A B : Type} [CommRing A] [Algebra S A] [CommRing B]
    [Algebra S B] (ψ : A →ₐ[S] B) (a : overAt (𝟙 (Sp S)) A ⟶ G') :
    algPtPush h B (Formalism.L2.Pj.homAt (𝟙 (Sp S)) ψ ≫ a) = Formalism.L2.Pj.homAt x0 ψ ≫ algPtPush h A a :=
  Over.OverMorphism.ext ((algPtPush_left h B _).trans ((Category.assoc (spMap (ψ : A →+* B)) a.left φ).trans
    (congrArg (fun q => spMap (ψ : A →+* B) ≫ q) (algPtPush_left h A a).symm)))

theorem algPtPush_comp (h : IsGrpPullback G' G x0 φ) {A : Type} [CommRing A] [Algebra S A]
    (u' : G' ⟶ G') (u : G ⟶ G) (e : u'.left ≫ φ = φ ≫ u.left) (a : overAt (𝟙 (Sp S)) A ⟶ G') :
    algPtPush h A (a ≫ u') = algPtPush h A a ≫ u :=
  Over.OverMorphism.ext ((algPtPush_left h A _).trans ((Category.assoc a.left u'.left φ).trans
    ((congrArg (fun q => a.left ≫ q) e).trans ((Category.assoc a.left φ u.left).symm.trans
      (congrArg (fun q => q ≫ u.left) (algPtPush_left h A a).symm)))))

end Push

theorem jetPoints_laws_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) ↔ (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx
  obtain rfl : x = fun m => algPtPush mp.cart _ (x' m) :=
    funext fun m => Over.OverMorphism.ext ((hx m).symm.trans (algPtPush_left mp.cart _ (x' m)).symm)
  refine ⟨forall_congr' fun m => ?_, fun F => forall_congr' fun m => ?_,
    fun act => forall_congr' fun m => forall_congr' fun b => ?_⟩
  · rw [← (algPtPush_injective mp.cart _).eq_iff, map_one, algPtPush_homAt]
  · rw [← (algPtPush_injective mp.cart _).eq_iff, map_mul, algPtPush_homAt]
    simp only [jptG, algPtPush_homAt]
  · rw [← (algPtPush_injective mp.cart _).eq_iff, algPtPush_homAt,
      algPtPush_comp mp.cart _ _ (mp.act b)]

end GlobalTheory
end
end

