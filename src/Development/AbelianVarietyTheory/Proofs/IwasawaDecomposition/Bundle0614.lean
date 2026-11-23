module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
section
set_option autoImplicit false

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam
open GlobalTheory.ArcQ GlobalTheory.FlagBundle Filter Topology

namespace GlobalTheory.FrameLift

open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {σ : c.F →+* ℂ} {r : ℕ}

theorem nonempty_unfWit {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) : Nonempty (UnfWit U) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := hU
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

theorem exists_transport {p q : CxPts (genStr Z) σ} (h : p = q) (G : EigFrame Z σ (p.1 ≫ genι Z)) :
    ∃ G' : EigFrame Z σ (q.1 ≫ genι Z), (∀ τ i, G'.v τ i = G.v τ i) ∧
      ∀ (M : EigMet Z σ) τ, M.gram q G' τ = M.gram p G τ := by
  subst h
  exact ⟨G, fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_coords {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) {b₀ : ReciprocityTheory.L2DbarEstimates.V n} (hb₀ : b₀ ∈ B)
    {s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hs : ∀ b ∈ B, s b ∈ (U.X k).dom)
    (hd : DifferentiableOn ℂ s B) (V : (gen Z).affineOpens) {φ : c.F →+* Γ(gen Z, V.1)}
    (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z))
    (hV : ∀ b (hb : b ∈ B), cxPt Z (U.un k ⟨s b, hs b hb⟩) ∈ ptsIn (genStr Z) σ V.1) :
    ∃ N : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ, (∀ τ a a', DifferentiableOn ℂ (fun b => N b τ a a') B) ∧
      ∀ b (hb : b ∈ B) (y : CxPts (genStr Z) σ), cxPt Z (U.un k ⟨s b, hs b hb⟩) = y →
        ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (G f : EigFrame Z σ (y.1 ≫ genι Z)),
          (∀ τ i, G.v τ i = (cxFrame Z (U.un k ⟨s b, hs b hb⟩)).v τ i) → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hy) f →
            ∀ τ, G.co f τ = N b τ := by
  classical
  obtain ⟨W⟩ := nonempty_unfWit hU
  let L := EuclideanSpace.equiv (Fin n) ℂ
  set B₁ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hB₁
  have hB₁o : IsOpen B₁ := hB.preimage L.symm.continuous
  let x : (Fin n → ℂ) → (U.X k).dom := fun v =>
    if h : L.symm v ∈ B then ⟨s (L.symm v), hs _ h⟩ else ⟨s b₀, hs _ hb₀⟩
  have hx : ∀ v ∈ B₁, (x v).1 = s (L.symm v) := fun v hv => by
    simp only [x, dif_pos (show L.symm v ∈ B from hv)]
  have hxL : ∀ b (hb : b ∈ B), x (L b) = ⟨s b, hs b hb⟩ := fun b hb =>
    Subtype.ext ((hx _ (by simpa [hB₁] using hb)).trans (by rw [ContinuousLinearEquiv.symm_apply_apply]))
  have hsd : DifferentiableOn ℂ (fun v => s (L.symm v)) B₁ := hd.comp L.symm.differentiableOn fun v hv => hv
  have hPd : ∀ a, DifferentiableOn ℂ (fun v => W.Pm k (x v) a) B₁ := fun a => differentiableOn_pi.2 fun j =>
    (GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun v => s (L.symm v)) (fun v hv => hs _ hv)
      (fun τ a a' => differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a') _ _ _).congr
      fun v hv => by rw [W.Pm_eq, hx v hv]
  let p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun v => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x v))
  have hu : ∀ v, W.F.u (W.ik k) (W.Pm k (x v)) =
      p v ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun v => (W.lie k (x v)).1.symm.trans (ptF_fst (U.un k (x v))).symm
  have hp : ∀ v, p v ≫ pullback.snd _ _ = spMap σ := fun v => ptF_snd (U.un k (x v))
  choose Y hY hYd using fun (a : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    GlobalTheory.ModelExpCoord.coord_holomorphic _ _ _ _ _ _ _ _ Z σ W.g _ W.F (W.ik k) n B₁ (fun v => W.Pm k (x v)) p hu V
      (Φ.v a.1 a.2) hB₁o (fun v => W.period k (x v)) hPd hp (Φ.tan a.1 a.2)
  refine ⟨fun b τ => of fun a a' => Y ⟨τ, a'⟩ (L b) (W.e.symm ⟨τ, a⟩), fun τ a a' => ?_, fun b hb y hq hy G f hG hf τ => ?_⟩
  · refine differentiableOn_pi.1 ((hY ⟨τ, a'⟩).comp L.differentiableOn fun b hb => ⟨by simpa [hB₁] using hb, ?_⟩) _
    show ⊤ ≤ (cxPt Z (U.un k (x (L b)))).1 ⁻¹ᵁ V.1
    rw [hxL b hb]
    exact hV b hb
  · ext a a'
    obtain ⟨w, hwt, hwm, hwc⟩ := GlobalTheory.HodgeSmooth.exists_lift_comb _ hq G f hG τ a'
    have h1 := hYd ⟨τ, a'⟩ (L b) (by simpa [hB₁] using hb) y hy (by
      show _ = (cxPt Z (U.un k (x (L b)))).1
      rw [hxL b hb, hq])
    have hfv : spMap (dualMap (evHom hy)) ≫ Φ.v τ a' = w ≫ Z.m.φ := by rw [hwm, hf τ a']
    rw [hfv] at h1
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      show _ = _ ≫ GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x (L b)))
      rw [hxL b hb]
      exact hwt.1
    have h2 := isDerivAt0_ex_of_push Z W.F (p (L b)) (W.ik k) (W.Pm k (x (L b))) (W.period k _) (hu _) hbase h1
    rw [hxL b hb] at h2
    have per := W.period k ⟨s b, hs b hb⟩
    obtain ⟨hPx, hv⟩ := W.lie k ⟨s b, hs b hb⟩
    have h3 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ per _ ((U.un k ⟨s b, hs b hb⟩).u τ) _ (hv τ) _
      _).1 (hPx ▸ hwc)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ per
    have h4 := congrFun ((tn.2.2 _ (tn.1 _ _ h2)).unique h2 h3) (W.e.symm ⟨τ, a⟩)
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    refine Eq.trans ?_ h4.symm
    simp [Finset.sum_apply, Pi.single_apply, hi]

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_regAt {y : CxPts X.str σ'} {g : X.Fn} (hg : RegAt (under y) g) : ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'} {A : Mat m X.Fn}
    (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem analyticAt_ratVal {d : ℕ} (ch : AlgChart X.str σ' d) {y : CxPts X.str σ'} (hy : y ∈ ch.e.source) {g : X.Fn}
    (hg : RegAt (under y) g) : AnalyticAt ℂ (fun w => ratVal g (ch.e.symm w)) (ch.e y) := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn ((ch.holo W a).congr fun w hw => ratVal_fnOf hw.2 _ a)
    ((GlobalTheory.ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)).mem_nhds ⟨ch.e.map_source hy, ?_⟩)
  show ch.e.symm (ch.e y) ∈ ptsIn X.str σ' W
  rw [ch.e.left_inv hy]
  exact mem_ptsIn.2 hW

end GlobalTheory.FrameLift

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

theorem GlobalTheory.FrameLift.exists_holomorphic_frame_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU X j f₀ Eb A₀ hj hoi hT y _ c' hyc A hA k' s hs hlift
  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.LieBase.coords_eq_ratVal_of_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have htend : Tendsto c'.e.symm (𝓝 (c'.e y)) (𝓝 y) := c'.e.tendsto_symm hyc
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1 ((hlift.and hs.eventually_analyticAt).and
    (htend.eventually (hVn.and (GlobalTheory.FrameLift.eventually_mem hA))))
  choose hsB hpt using fun b hb => (hBall b hb).1.1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k' hB hb₀ hsB
    (fun b hb => (hBall b hb).1.2.differentiableAt.differentiableWithinAt) V Φ
    (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k' ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (c'.e.symm b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (c'.e.symm b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (c'.e.symm b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (c'.e.symm b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (c'.e.symm b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (GlobalTheory.FrameLift.analyticAt_ratVal c' hyc ((hM y hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N (c'.e y) τ * (M τ).map fun r => ratVal r (c'.e.symm (c'.e y))).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    refine ⟨hex b hb, fun hsb g hg Me τ => ?_⟩
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjective
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem exists_bilinForm_descend_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (hf : Function.Surjective f) (β : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x, f x = 0 → ∀ y, β x y = 0) (h2 : ∀ x, f x = 0 → ∀ y, β y x = 0) :
    ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  classical
  set g := Function.surjInv hf with hgdef
  have hg : ∀ y, f (g y) = y := Function.surjInv_eq hf
  have key1 : ∀ a b, f a = f b → ∀ y, β a y = β b y := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h1 (a - b) hk y
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have key2 : ∀ a b, f a = f b → ∀ y, β y a = β y b := by
    intro a b h y
    have hk : f (a - b) = 0 := by rw [map_sub, h, sub_self]
    have := h2 (a - b) hk y
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨LinearMap.mk₂ ℤ (fun y y' => β (g y) (g y')) ?_ ?_ ?_ ?_, ?_⟩
  · intro y1 y2 y'
    rw [key1 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add (f := _), hg, hg, hg]), map_add (f := _),
      LinearMap.add_apply]
  · intro c y y'
    rw [key1 (g (c • y)) (c • g y) (by rw [map_zsmul, hg, hg]), map_smul, LinearMap.smul_apply]
  · intro y y1 y2
    rw [key2 (g (y1 + y2)) (g y1 + g y2) (by rw [map_add (f := _), hg, hg, hg]), map_add (f := _)]
  · intro c y y'
    rw [key2 (g (c • y')) (c • g y') (by rw [map_zsmul, hg, hg]), map_smul]
  · intro x y
    rw [LinearMap.mk₂_apply, key1 (g (f x)) x (hg _), key2 (g (f y)) y (hg _)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeans
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Formulas

variable {X : Type} [AddCommGroup X]

theorem evalW_add_left (w w' : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (w + w') B = evalW w B + evalW w' B := by
  unfold evalW
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

theorem evalW_zero_left (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW (0 : (X × X) →₀ ℤ) B = 0 := by
  simp [evalW]

theorem evalW_zsmul_left (k : ℤ) (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (k • w) B = k * evalW w B := by
  unfold evalW
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ => ?_
  simp only [smul_eq_mul, Int.cast_mul]
  ring

theorem evalW_single_left (p : X × X) (k : ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (Finsupp.single p k) B = k * B p.1 p.2 := by
  unfold evalW
  exact Finsupp.sum_single_index (by simp)

theorem evalW_finset_sum_left {ι : Type} (s : Finset ι) (f : ι → (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (∑ i ∈ s, f i) B = ∑ i ∈ s, evalW (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalW_zero_left]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evalW_add_left, ih]

theorem evalW_lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (lamW D N n 𝓜 r w a) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y))) := by
  simp only [lamW, evalW_zsmul_left, evalW_add_left, evalW_finset_sum_left, evalW_single_left]
  push_cast
  simp

theorem kDen_mul_evalR_baseFun {O : Type} [CommRing O] [Module.Finite ℤ O] [Module O X] [Module.Finite O X]
    [Module.Finite ℤ X] (D : ℕ) (φ : InvFun ℤ) (N n : ℕ) (𝓜 : Finset ℕ) {r : (Fin n → ℤ) →ₗ[ℤ] X}
    (hr : Function.Surjective r) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (kDen N n 𝓜 : ℝ) * evalR (baseFun O D φ 𝓜) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, classMin M (fun x z => B (r x) (r z)) y) := by
  have hE : ∀ M, (fineMean M).eval X (fun x z => B x z) =
      (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    intro M
    rw [(fineMean M).eval_eq hr]
    simp [fineMean]
  have key : ∀ M ∈ 𝓜, (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (((M : ℝ) + 1) ^ n)⁻¹ =
      ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := by
    intro M hM
    rw [← Finset.mul_prod_erase 𝓜 (fun M : ℕ => ((M : ℝ) + 1) ^ n) hM]
    have : ((M : ℝ) + 1) ^ n ≠ 0 := by positivity
    field_simp
  have hs : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y =
      ∑ M ∈ 𝓜, (∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun M hM => by rw [← mul_assoc, key M hM]
  have h1 : evalR (baseFun O D φ 𝓜) B = D * (evalR φ B + ∑ M ∈ 𝓜, (fineMean M).eval X (fun x z => B x z)) :=
    eval_baseFun D φ 𝓜 _
  rw [h1]
  simp only [hE, kDen]
  push_cast
  calc _ = (D : ℝ) * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) + N * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y)) := by ring
    _ = _ := by
      rw [hs, Finset.mul_sum]
      simp only [mul_assoc]

theorem classMin_le_of_nonneg (M : ℕ) {n : ℕ} {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (hB : ∀ x, 0 ≤ B x x)
    {y : Fin n → ZMod (M + 1)} {x : Fin n → ℤ} (hx : redV M x = y) : classMin M B y ≤ B x x :=
  csInf_le ⟨0, by rintro _ ⟨b, -, rfl⟩; exact hB b⟩ ⟨x, hx, rfl⟩

end Formulas

theorem exists_contact_baseFun_lamW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  intro E _ _ _ H D φs 𝓜 X _ _ _ _ N m n u w r a hD hφ hN hu hS hr ha
  classical
  choose F hF using fun (M : ℕ) (y : Fin n → ZMod (M + 1)) =>
    _root_.GlobalTheory.dickson_finite_below_every m (fun a' : {a' : Fin n → ℤ // redV M a' = y} => fun j => (u j (r a'.1) (r a'.1)).toNat)
  let vec : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → (Fin n → ℤ) → Fin m → ℤ :=
    fun M y a' i => u i (r (a M y)) (r (a M y)) - u i (r a') (r a')
  have hI := GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φs N m u w hφ hu hS
  have hsum : ∀ (t : Fin m → ℝ) (x z : X), (∑ i, t i • toReal (u i)) x z = ∑ i, t i * (u i x z : ℝ) := by
    intro t x z
    simp [LinearMap.sum_apply]
  have hP : 0 < ∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n := Finset.prod_pos fun _ _ => by positivity
  have hc : ∀ M ∈ 𝓜, 0 < (N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := fun M _ =>
    mul_pos (by exact_mod_cast hN) (Finset.prod_pos fun _ _ => by positivity)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD

  have hle_gen : ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X),
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B ≤ evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW]
    have h1 := ((hI.2 B hB).1)
    have h2 : ∀ M ∈ 𝓜, ∑ y, classMin M (fun x z => B (r x) (r z)) y ≤ ∑ y, B (r (a M y)) (r (a M y)) :=
      fun M _ => Finset.sum_le_sum fun y _ =>
        classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB (r x)) (ha M y)
    have h3 := Finset.sum_le_sum fun M hM => mul_le_mul_of_nonneg_left (h2 M hM) (hc M hM).le
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    exact mul_le_mul_of_nonneg_left (add_le_add h4 h3) hD'.le

  have hback : ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) →
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB hcl
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW, hI.1 B hB]
    congr 2
    exact Finset.sum_congr rfl fun M hM => by rw [Finset.sum_congr rfl fun y _ => hcl M hM y]
  refine ⟨⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
      (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _), ?_, ?_, ?_, ?_, hback⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet 𝓜) fun M _ =>
      Set.finite_iUnion fun y => (Finset.finite_toSet _).image _
  · intro β hβ hβ0
    have hB : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
      have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
        (fun i y => by fin_cases i; simpa using hβ0 y) (fun i => by fin_cases i; simp)
      simpa using this
    rw [← evalR_toReal]
    exact hle_gen _ (GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB)
  · intro B hB heq
    have hB' := GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW] at heq
    have heq' := mul_left_cancel₀ hD'.ne' heq
    have h1 := (hI.2 B hB').1
    have hy : ∀ M, ∀ y, 0 ≤ B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y := fun M y =>
      sub_nonneg.2 (classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) (ha M y))
    have hT : 0 ≤ ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) :=
      Finset.sum_nonneg fun M hM => mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)
    have hT' : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) =
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y)) -
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
          ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_sub_distrib, mul_sub]
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    have hT0 : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) = 0 := by
      linarith
    have hW : (N : ℝ) * evalR φs B = evalW w B := by
      have : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φs B) = (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B := by
        linarith
      exact mul_left_cancel₀ hP.ne' this
    have hcl : ∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y)) := by
      intro M hM y
      have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun M hM =>
        mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)).1 hT0 M hM
      have e2 := (mul_eq_zero.1 e1).resolve_left (hc M hM).ne'
      have e3 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hy M y).1 e2 y (Finset.mem_univ _)
      linarith
    have hcm : ∀ M y (x : Fin n → ℤ), redV M x = y → classMin M (fun x z => B (r x) (r z)) y ≤ B (r x) (r x) :=
      fun M y x hx => classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) hx
    obtain ⟨t, ht0, rfl⟩ := (hI.2 B hB').2 hW
    refine ⟨t, ht0, ?_, rfl⟩
    intro v hv
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨M, hM, y, a', ha'F, rfl⟩ := hv
    have e := hcl M hM y
    have e' := hcm M y a'.1 a'.2
    rw [e, hsum, hsum] at e'
    rw [hsum] at e
    have : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    rw [this]
    linarith
  · intro t ht hA
    refine hback _ ⟨t, ht, rfl⟩ fun M hM y => ?_
    refine IsLeast.csInf_eq ⟨⟨a M y, ha M y, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a', ha'F, hle⟩ := hF M y ⟨x, hx⟩
    have hmem : vec M y a'.1 ∈ ⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
        (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _) := by
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
      exact ⟨M, hM, y, a', ha'F, rfl⟩
    have h1 := hA _ hmem
    have h2 : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    have h3 : ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) ≤ ∑ i, t i * (u i (r x) (r x) : ℝ) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have p1 := hu.nonneg i (r a'.1)
      have p2 := hu.nonneg i (r x)
      have p3 : (u i (r a'.1) (r a'.1)).toNat ≤ (u i (r x) (r x)).toNat := hle i
      exact_mod_cast (show u i (r a'.1) (r a'.1) ≤ u i (r x) (r x) by omega)
    show (∑ i, t i • toReal (u i)) (r (a M y)) (r (a M y)) ≤ (∑ i, t i • toReal (u i)) (r x) (r x)
    rw [hsum, hsum]
    linarith

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellFace

theorem exists_face_form : ∀ {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m n : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → IsCell bar ψ γ' → (∀ j, InRCone γ (γ' j)) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (γ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 → InRCone γ' β := by
  intro O _ bar ψ X _ _ _ m n γ γ' hγ hγ' hin
  exact exists_cut_of_cell_le O bar ψ X m n γ γ' hγ hγ' hin

end GlobalTheory.PolFan.CellFace
end
end

