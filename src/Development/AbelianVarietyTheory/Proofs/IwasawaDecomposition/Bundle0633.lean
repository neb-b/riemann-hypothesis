module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameChangeAlongAnalyticLift
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology
open GlobalTheory.PointChern

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrameChange

theorem isHolTo_cxPt_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}
    {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (x : ReciprocityTheory.L2DbarEstimates.V n → (U.X k).dom)
    (hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  let L := EuclideanSpace.equiv (Fin n) ℂ
  have hB₁ : IsOpen (L.symm ⁻¹' B) := hB.preimage L.symm.continuous
  have h1 := GlobalTheory.GramFamily.isHolTo_cxPt Z hU k hB₁ (fun u => x (L.symm u)) fun τ a a' =>
    (hd τ a a').comp L.symm.differentiableOn fun u hu => hu
  intro W f
  obtain ⟨ho, hdf⟩ := h1 W f
  have hset : {b ∈ B | ⊤ ≤ (cxPt Z (U.un k (x b))).1 ⁻¹ᵁ W} =
      L ⁻¹' {u ∈ L.symm ⁻¹' B | ⊤ ≤ (cxPt Z (U.un k (x (L.symm u)))).1 ⁻¹ᵁ W} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
  rw [hset]
  refine ⟨ho.preimage L.continuous, ?_⟩
  have := hdf.comp L.differentiableOn (Set.mapsTo_preimage _ _)
  refine this.congr fun b _ => ?_
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end GlobalTheory.UnifFrameChange


open GlobalTheory.UnifFrameChange in
theorem GlobalTheory.UnifFrameChange.exists_holomorphic_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q), AnalyticAt ℂ s v → (∀ᶠ w in nhds v, ∃ hs : s w ∈ (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) v) ∧ (∀ τ, IsUnit (K v τ).det) ∧ ∀ᶠ w in nhds v, ∀ (hs : s w ∈ (U.X k).dom) (g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v _ A hA s han hlift
  classical

  set pt : ReciprocityTheory.L2DbarEstimates.V X.dim → CxPts X.str (σ.comp e.toRingHom) := fun w => ψ (GlobalTheory.UnifDens.flatL h w) with hptdef

  obtain ⟨B₀, hB₀all, hB₀, hv₀⟩ := eventually_nhds_iff.1 (hlift.and han.eventually_analyticAt)
  choose hsB₀ hflB₀ using fun b (hb : b ∈ B₀) => (hB₀all b hb).1
  have hpt₀ : ∀ b (hb : b ∈ B₀), cxPt T.Z (U.un k ⟨s b, hsB₀ b hb⟩) = cxOf e σ hj (pt b) := by
    intro b hb
    have := hψ ⟨s b, hsB₀ b hb⟩
    rw [hflB₀ b hb] at this
    exact this.symm
  let x : ReciprocityTheory.L2DbarEstimates.V X.dim → (U.X k).dom := fun b =>
    if hb : b ∈ B₀ then ⟨s b, hsB₀ b hb⟩ else ⟨s v, hsB₀ v hv₀⟩
  have hxB : ∀ b (hb : b ∈ B₀), x b = ⟨s b, hsB₀ b hb⟩ := fun b hb => by simp only [x, dif_pos hb]
  have hsd : DifferentiableOn ℂ s B₀ := fun b hb => (hB₀all b hb).2.differentiableAt.differentiableWithinAt
  have hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B₀ := by
    intro τ a a'
    refine (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a').congr fun b hb => ?_
    rw [hxB b hb]
    rfl
  have hY := isHolTo_cxPt_V T.Z hU k hB₀ x hd
  have hxpt : ∀ b (hb : b ∈ B₀), (cxPt T.Z (U.un k (x b))) = cxOf e σ hj (pt b) := fun b hb => by
    rw [hxB b hb]; exact hpt₀ b hb

  have hgenev : ∀ W' : (gen T.Z).Opens, cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ W' →
      ∀ᶠ w in 𝓝 v, w ∈ B₀ ∧ ⊤ ≤ (cxPt T.Z (U.un k (x w))).1 ⁻¹ᵁ W' := by
    intro W' hW'
    refine ((hY W' 0).1).mem_nhds ⟨hv₀, ?_⟩
    show ⊤ ≤ (cxPt T.Z (U.un k (x v))).1 ⁻¹ᵁ W'
    rw [hxpt v hv₀]
    exact hW'
  have hpre : ∀ (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) W ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ (j ''ᵁ W) := by
    intro W z
    have := mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl) (U := j ''ᵁ W) (z := z)
    rwa [j.preimage_image_eq W] at this
  have hXev : ∀ W : X.X.Opens, pt v ∈ ptsIn X.str (σ.comp e.toRingHom) W →
      ∀ᶠ w in 𝓝 v, pt w ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
    intro W hW
    filter_upwards [hgenev _ ((hpre W _).1 hW)] with w hw
    refine (hpre W _).2 ?_
    rw [← hxpt w hw.1]
    exact hw.2
  have hregev : ∀ {g : X.Fn}, RegAt (under (pt v)) g → ∀ᶠ w in 𝓝 v, RegAt (under (pt w)) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [hXev W (mem_ptsIn.2 hW)] with w hw
    exact regAt_fnOf (mem_ptsIn.1 hw) _ a
  have hmemev : ∀ᶠ w in 𝓝 v, A ∈ Eb.S (under (pt w)) := by
    obtain ⟨U', B', hU', hB', hS⟩ := Eb.loc (under (pt v))
    have hP := (hS _ hU' A).1 hA
    have hU'' : ∀ᶠ w in 𝓝 v, under (pt w) ∈ U' := by
      filter_upwards [hXev U' (mem_ptsIn.2 hU')] with w hw
      exact mem_ptsIn.1 hw
    have h1 : ∀ᶠ w in 𝓝 v, ∀ τ, (∀ i j, RegAt (under (pt w)) ((A * B'⁻¹) τ i j)) ∧
        RegAt (under (pt w)) ((A * B'⁻¹) τ).det⁻¹ :=
      Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        hregev (mem_O_ratOf.1 ((hP τ).1 i j))).and (hregev (mem_O_ratOf.1 (hP τ).2.2.1))
    filter_upwards [hU'', h1] with w hw hw1
    exact (hS _ hw A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hw1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hw1 τ).2,
      fun i j hi => absurd hi (by simp)⟩
  have hratan : ∀ {g : X.Fn}, RegAt (under (pt v)) g → AnalyticAt ℂ (fun w => ratVal g (pt w)) v := by
    intro g hg
    haveI : IsOpenImmersion j := hoi
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    set g' := (j.appIso W).inv.hom a
    have hvS : v ∈ {b ∈ B₀ | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ W)} := by
      refine ⟨hv₀, ?_⟩
      rw [hxpt v hv₀]
      exact GlobalTheory.LieBase.le_preimage_cxOf e σ hj W (mem_ptsIn.2 hW)
    have han' := GlobalTheory.SCV.analyticAt_of_differentiableOn ((hY (j ''ᵁ W) g').2) (((hY (j ''ᵁ W) g').1).mem_nhds hvS)
    refine han'.congr ?_
    filter_upwards [hXev W (mem_ptsIn.2 hW), hB₀.mem_nhds hv₀] with w hw hwB
    show valAt' _ _ _ = ratVal _ (pt w)
    rw [ratVal_fnOf hw, GlobalTheory.LieBase.ev_eq_valAt'_cxOf e σ hj W a hw, hxpt w hwB]

  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj (pt v)).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.LieBase.coords_eq_ratVal_of_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hVn : ∀ᶠ w in 𝓝 v, cxOf e σ hj (pt w) ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [hgenev _ hyV] with w hw
    rw [← hxpt w hw.1]
    exact hw.2
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1
    ((show ∀ᶠ w in 𝓝 v, w ∈ B₀ from hB₀.mem_nhds hv₀).and (hVn.and hmemev))
  have hsB : ∀ b ∈ B, s b ∈ (U.X k).dom := fun b hb => hsB₀ b (hBall b hb).1
  have hpt : ∀ b (hb : b ∈ B), cxPt T.Z (U.un k ⟨s b, hsB b hb⟩) = cxOf e σ hj (pt b) :=
    fun b hb => hpt₀ b (hBall b hb).1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k hB hb₀ hsB
    (hsd.mono fun b hb => (hBall b hb).1) V Φ (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (pt b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (pt b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (pt b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (pt b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (pt b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (pt b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (hratan ((hM (pt v) hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N v τ * (M τ).map fun r => ratVal r (pt v)).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    intro hsb g hg Me τ
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntFormStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d → y ≠ 0 → toReal x = d • toReal y →
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  first | exact @GlobalTheory.posReal_multiple_rat | exact GlobalTheory.posReal_multiple_rat | (intros; apply GlobalTheory.posReal_multiple_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalSymplecticBasisAdaptedCoisotropic
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymplecticNormalForm

theorem key_apply {a b r : ℕ} (A : Matrix (Fin a) (Fin r) ℚ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (B : Matrix (Fin b) (Fin r) ℚ) (i : Fin a) (j : Fin b) :
    (A * Mq * Bᵀ) i j = A i ⬝ᵥ Mq *ᵥ B j := by
  rw [Matrix.mul_apply, dotProduct_mulVec]
  simp only [Matrix.transpose_apply, dotProduct, vecMul, Matrix.mul_apply]

theorem skew_swap {r : ℕ} (Mq : Matrix (Fin r) (Fin r) ℚ) (h : Mqᵀ = -Mq) (x y : Fin r → ℚ) :
    x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, h, dotProduct_comm, Matrix.neg_mulVec, dotProduct_neg]

theorem exists_adapted_rational_symplectic_basis : ∀ (g r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ), r = 2 * g → Mᵀ = -M → M.det ≠ 0 → LinearIndependent ℚ (fun i j => (c i j : ℚ)) → (∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (c i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (c i j : ℝ))) → ∃ (rk : ℕ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ), rk ≤ g ∧ (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 ∧ (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) ∧ (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) ∧ (∀ m (j : Fin g), j.val < rk → dl m j = 0) ∧ c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ := by
  intro g r r₀ M c hr hskew hdet hind hreal
  set Mq : Matrix (Fin r) (Fin r) ℚ := M.map (Int.cast : ℤ → ℚ) with hMq
  set cq : Matrix (Fin r₀) (Fin r) ℚ := c.map (Int.cast : ℤ → ℚ) with hcq
  have hskq : Mqᵀ = -Mq := by
    ext i j
    have := congrArg (fun A => A i j) hskew
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp only [hMq, Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply]
    exact_mod_cast this
  have hdq : Mq.det ≠ 0 := by
    rw [hMq, ← Int.cast_det]
    exact_mod_cast hdet
  set V : Submodule ℚ (Fin r → ℚ) := Submodule.span ℚ (Set.range fun i j => (c i j : ℚ)) with hVdef
  have hcqV : ∀ m, cq m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩
  have hV : ∀ v : Fin r → ℚ, (∀ w ∈ V, v ⬝ᵥ Mq *ᵥ w = 0) → v ∈ V := by
    intro v hv
    apply GlobalTheory.T.rat_mem_span_of_real_mem_span_fin r₀ r (fun i j => (c i j : ℚ)) v
    have hfun : (fun i j => (((c i j : ℚ)) : ℝ)) = fun i j => (c i j : ℝ) := by
      funext i j; simp
    rw [hfun]
    apply hreal
    intro i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hv _ (hcqV i))
    simp only [dotProduct, mulVec, hMq, hcq, Matrix.map_apply] at h ⊢
    push_cast at h ⊢
    exact h
  let I : Submodule ℚ (Fin r → ℚ) :=
    { carrier := {y | ∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0}
      add_mem' := by
        intro a b ha hb w hw
        simp only [Set.mem_setOf_eq] at ha hb
        rw [add_dotProduct, ha w hw, hb w hw, add_zero]
      zero_mem' := by intro w _; simp
      smul_mem' := by
        intro t a ha w hw
        simp only [Set.mem_setOf_eq] at ha
        rw [smul_dotProduct, ha w hw, smul_zero] }
  have hmemI : ∀ y, y ∈ I ↔ ∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0 := fun y => Iff.rfl
  have hIiso : ∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0 :=
    fun x hx y hy => (hmemI x).mp hx y (hV y ((hmemI y).mp hy))
  obtain ⟨L, hIL, hLiso, hLdim⟩ := _root_.GlobalTheory.exists_lagrangian_containing_isotropic_rat g r Mq I hr hskq hdq hIiso
  have hLV : ∀ x ∈ L, x ∈ V := fun x hx =>
    _root_.GlobalTheory.rat_alternating_orthogonal_orthogonal_le r Mq V hskq hdq x (fun y hy => hLiso x hx y (hIL ((hmemI y).mpr hy)))
  obtain ⟨rk, hrk, ε, hεind, hεL, hεI, hIspan⟩ := GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace g r I L hIL hLdim
  have hεiso : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0 := fun i j => hLiso _ (hεL i) _ (hεL j)
  have hεV : ∀ i, ε i ∈ V := fun i => hLV _ (hεL i)
  have hεperp : ∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0 :=
    fun i hi => (hmemI _).mp (hεI i hi)
  have hψ : ∀ j : Fin g, ∃ x : Fin r → ℚ, (rk ≤ j.val → x ∈ V) ∧
      ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
    intro j
    by_cases hj : rk ≤ j.val
    · obtain ⟨x, hxV, hx⟩ := _root_.GlobalTheory.dualV_pairing_exists r g rk Mq V ε hskq hεind hεperp
        (fun y hy => hIspan y ((hmemI y).mpr hy)) j hj
      exact ⟨x, fun _ => hxV, hx⟩
    · obtain ⟨x, hx⟩ := _root_.GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent r g Mq ε hdq hεind (fun i => if i = j then 1 else 0)
      exact ⟨x, fun h => absurd h hj, hx⟩
  choose ψ hψV hψε using hψ
  obtain ⟨φ, hφiso, hφε, hφψ⟩ := GlobalTheory.T.exists_isotropic_dual_of_skew_matrix' r g Mq ε ψ hskq hεiso (fun i j => hψε j i)
  have hspanV : Submodule.span ℚ (Set.range ε) ≤ V :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hεV i)
  have hφV : ∀ j : Fin g, rk ≤ j.val → φ j ∈ V := fun j hj => by
    have := V.add_mem (hspanV (hφψ j)) (hψV j hj)
    simpa using this
  have hα : ∀ i, ∃ a : Fin r₀ → ℚ, ∑ m, a m • (fun k => (c m k : ℚ)) = ε i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hεV i)
  choose α hα using hα
  have hβ : ∀ j : Fin g, ∃ b : Fin r₀ → ℚ, rk ≤ j.val → ∑ m, b m • (fun k => (c m k : ℚ)) = φ j := by
    intro j
    by_cases hj : rk ≤ j.val
    · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hφV j hj)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose β hβ using hβ
  let αm : Matrix (Fin g) (Fin r₀) ℚ := α
  let εm : Matrix (Fin g) (Fin r) ℚ := ε
  let φm : Matrix (Fin g) (Fin r) ℚ := φ
  let βm : Matrix (Fin g) (Fin r₀) ℚ := β
  have hαc : αm * cq = εm := by
    ext i k
    have h1 := congrFun (hα i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    show (αm * cq) i k = ε i k
    rw [← h1, Matrix.mul_apply]
    rfl
  refine ⟨rk, αm, φm, βm,
    Matrix.of fun m i => -(cq m ⬝ᵥ Mq *ᵥ φ i), Matrix.of fun m j => cq m ⬝ᵥ Mq *ᵥ ε j,
    hrk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hαc]; ext i j; rw [key_apply]; exact hεiso i j
  · ext i j; rw [key_apply]; exact hφiso i j
  · rw [hαc]; ext i j; rw [key_apply, Matrix.one_apply]
    rw [hφε j i]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro i hi m
    rw [hαc, key_apply]
    exact hεperp i hi _ (hcqV m)
  · intro j hj m
    have h1 := congrFun (hβ j hj) m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    show φ j m = (βm * cq) j m
    rw [← h1, Matrix.mul_apply]
    rfl
  · intro m j hj
    simp only [Matrix.of_apply]
    rw [skew_swap Mq hskq, hεperp j hj _ (hcqV m), neg_zero]
  · rw [hαc]
    ext m k
    have h := congrFun (_root_.GlobalTheory.coords_in_rational_symplectic_basis g r Mq ε φ hr hskq hdq hεiso hφiso hφε (cq m)) k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    exact h

end GlobalTheory.SymplecticNormalForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabelling
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

theorem exists_isTwInv_simpLab_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  intro E _ _ _ H q φ lab w ψ' hDom hφ hlab hSL hw hC _ _ hS
  refine ⟨starLab lab w, isTwInv_starLab H hlab hw,
    fun X _ _ _ _ hX β hβ hp k hk => starLab_evalZ_smul lab w β hk (hSL.1 X hX β hβ hp k hk),
    fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  rcases hS.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hfree, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb₀, hp₀, hw₀, hin₀, hf, hpos, hin⟩
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m δ γ hδ hγ hγδ
    obtain ⟨m₂, s, hfs⟩ := exists_isFaceCut δ g hg1
    have hδs : IsCell H.bar φ (fun j => δ (s j)) := _root_.GlobalTheory.PolFan.isCell_face_of_isFaceCut E H q φ hφ X hX (hDom X) m₁ δ hδ m₂ s g hfs
    have hfree' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (fun j => δ (s j)) β → w.evalZ β = 0 :=
      fun β hb hp hc => hfree β hb hp (hg3 β hb hp (inRCone_of_sub s hc) (IsFaceCut.apply_eq_zero hfs hc))
    have hcell' := hS.1 X hX m₂ _ hδs hfree'
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδs.mem j) (hδs.nonneg j) hc
      have := hfree' β' hb' hp' (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s j)) j) ht.le e)
      rw [hw'] at this
      norm_num at this
    refine ⟨m₂, _, hcell', hli.comp _ s.injective, fun i j hij => ?_, fun j => ?_⟩
    · simp only [starLab_evalZ_of_not lab w (hnc i), starLab_evalZ_of_not lab w (hnc j)] at hij
      exact s.injective (hinj (Real.exp_injective (by linarith)))
    · exact inRCone_trans (fun k => inRCone_face hfs (hγδ k) (hg2 k)) (hin j)
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    have hγs : IsCell H.bar φ (fun j => γ (s j)) := _root_.GlobalTheory.PolFan.isCell_face_of_isFaceCut E H q φ hφ X hX (hDom X) m γ hγ m' s h hf
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m' δ (fun j => γ (s j)) hδ hγs (fun k => hγδ (s k))
    obtain ⟨m₂, s', hfs⟩ := exists_isFaceCut δ g hg1
    have hβ₀δ : InRCone δ β₀ := inRCone_trans hγδ hin₀
    have hgpos : 0 < g β₀ := by
      rcases (hβ₀δ.apply_nonneg g hg1).lt_or_eq with h' | h'
      · exact h'
      · exact (hpos.ne' (IsFaceCut.apply_eq_zero hf (hg3 β₀ hb₀ hp₀ hβ₀δ h'.symm))).elim
    have hcell' := hS.2.1 X hX m₁ δ hδ β₀ hb₀ hp₀ hw₀ hβ₀δ m₂ s' g hfs hgpos
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s' j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδ.mem (s' j)) (hδ.nonneg (s' j)) hc
      have hβ'δ : InRCone δ β' := InRCone.of_toReal_eq_smul (inRCone_self δ (s' j)) ht.le e
      have heq : β' = β₀ := (hC X hX).2.2 m₁ δ hδ β' hb' hp' β₀ hb₀ hp₀ hw' hw₀ hβ'δ hβ₀δ
      have h0 : g β' = 0 := IsFaceCut.apply_eq_zero hfs (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s' j)) j) ht.le e)
      rw [heq] at h0
      exact hgpos.ne' h0
    have hv0 : (starLab lab w).evalZ β₀ = -1 := starLab_evalZ_of_eq_one lab w hw₀
    have hvs : ∀ j, (starLab lab w).evalZ (δ (s' j)) = Real.exp (lab.evalZ (δ (s' j))) - 1 :=
      fun j => starLab_evalZ_of_not lab w (hnc j)
    have hsp : Submodule.span ℤ (Set.range fun j => δ (s' j)) ≤ LinearMap.ker g :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.2 ((hfs.2 (s' j)).2 ⟨j, rfl⟩))
    have hself : ∀ j, InRCone (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) (δ (s' j)) :=
      fun j => by simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) j.succ
    refine ⟨m₂ + 1, Fin.cons β₀ fun j => δ (s' j), hcell', ?_, ?_, fun j => ?_⟩
    · refine LinearIndependent.finCons' β₀ _ (hli.comp _ s'.injective) fun c y hy hz => ?_
      have h1 : g y = 0 := LinearMap.mem_ker.1 (hsp hy)
      have h2 := congrArg g hz
      rw [map_add (f := _), map_smul, h1, add_zero, map_zero, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_right hgpos.ne'
    · intro i j hij
      simp only at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' j)))]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' i)))]
        | succ j =>
          simp only [Fin.cons_succ, hvs] at hij
          exact congrArg Fin.succ (s'.injective (hinj (Real.exp_injective (by linarith))))
    · refine inRCone_trans (fun k => ?_) (hin j)
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) 0
      · simp only [Fin.cons_succ]
        exact inRCone_trans hself (inRCone_face hfs (hγδ (s k)) (hg2 k))

end GlobalTheory.PolFan.StarLab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationEqConjMul
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem hermForm_im_intComb : ∀ (g r r' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r' → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ i j, (hermForm Hm (w i) (w j)).im = ((c * M * cᵀ) i j : ℝ) := by
  intro g r r' Hm l w c M hw hM i j
  rw [hw i, hw j, hermForm_im_sum]
  simp only [hM]
  push_cast [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core
end

