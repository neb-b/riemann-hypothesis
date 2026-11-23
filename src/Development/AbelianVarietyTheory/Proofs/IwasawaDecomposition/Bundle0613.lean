module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinitePolFanConesCoverRealCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

open GlobalTheory.PolFan

theorem exists_finite_cover_rcone : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := by
  intro X _ _ φ N p P hφ hcov hsym hpos
  let ι : Type := {x : Σ m : ℕ, (Fin m → LinearMap.BilinForm ℤ X) × ((X × X) →₀ ℤ) //
    IsCone (id : ℤ → ℤ) φ x.2.1 ∧ StrictWith (id : ℤ → ℤ) φ N (linW x.2.2) x.2.1}
  have hnn : ∀ (x : ι) i, 0 ≤ linW x.1.2.2 (P i) := by
    intro x i
    have h1 := x.2.2.2.1 (P i) (mem_balForms_int.2 (hsym i)) (hpos i)
    have h2 := hφ.evalZ_nonneg (mem_balForms_int.2 (hsym i)) (hpos i)
    have : (0 : ℝ) ≤ (linW x.1.2.2 (P i) : ℝ) := le_trans (mul_nonneg (Nat.cast_nonneg _) h2) h1
    exact_mod_cast this
  let f : ι → Fin p → ℕ := fun x i => (linW x.1.2.2 (P i)).toNat
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.dickson_finite_below_every p f
  let e := F.equivFin
  let g : Fin F.card → ι := fun k => (e.symm k : ι)
  refine ⟨F.card, fun k => (g k).1.1, fun k => (g k).1.2.1, fun k => (g k).1.2.2, fun k => (g k).2, ?_⟩
  intro B hB hBp
  obtain ⟨m, u, w, hc, hs, hBu⟩ := hcov B hBp
  let i₀ : ι := ⟨⟨m, u, w⟩, hc, hs⟩
  obtain ⟨j, hjF, hj⟩ := hF i₀
  refine ⟨e ⟨j, hjF⟩, ?_⟩
  have hg : g (e ⟨j, hjF⟩) = j := by simp [g]
  show B ∈ rcone (g (e ⟨j, hjF⟩)).1.2.1
  rw [hg]
  obtain ⟨t, ht, rfl⟩ := hB
  have A := (GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φ N m u w hφ hc hs).1 _ hBu
  have C := (GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φ N j.1.1 j.1.2.1 j.1.2.2 hφ j.2.1 j.2.2).2 _ hBp
  apply C.2
  have hle : evalW j.1.2.2 (∑ i, t i • toReal (P i)) ≤ evalW w (∑ i, t i • toReal (P i)) := by
    rw [evalW_sum, evalW_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
    have h1 := hj i
    have h2 := hnn j i
    have h3 := hnn i₀ i
    simp only [f] at h1
    have : linW j.1.2.2 (P i) ≤ linW w (P i) := by
      have h3' : 0 ≤ linW w (P i) := h3
      have h1' : (linW j.1.2.2 (P i)).toNat ≤ (linW w (P i)).toNat := h1
      omega
    exact_mod_cast this
  linarith [C.1]

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloCoordFrameAt
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_holo_coord_frameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∀ (kU : U.Comp) (G : V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X kU).Ψ (Dw.p + Dw.q)), (∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u)) → (∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → ∃ M : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => M u a b) u) ∧ IsUnit (M (c'.e y)).det ∧ ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g) ∧ ∀ (x : Sp ℂ ⟶ T.Z.X) (g : EigFrame T.Z σ x), FrameAt e f₀ A₀ A (c'.e.symm u) g → ∀ i, IsCombAtG T.Z.t ((cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z) ((cxFrame T.Z (U.un kU ⟨G u, h⟩)).v τ.1) (fun b => M u b i) (g.v τ.1 i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y _ c' hyc A hA τ kU G hF hG
  obtain ⟨-, -, hTd⟩ := hLie
  obtain ⟨W, hW, φ, fW, hyW, hnear⟩ := _root_.GlobalTheory.NearFrame.exists_affine_frame_near E H Dw l Xo c O β T.Z F e σ X j f₀ Eb A₀ hj hTd y A hA
  classical
  let ev : V X.dim → (Γ(X.X, W) →+* ℂ) := fun u =>
    if h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W then evHom h else evHom hyW
  have hev : ∀ u (h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W), ev u = evHom h := fun u h => dif_pos h
  set S : Set (V X.dim) := c'.e.target ∩ c'.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W with hSdef
  have hSo : IsOpen S := c'.e.continuousOn_symm.isOpen_inter_preimage c'.e.open_target (isOpen_ptsIn _)
  have hu0 : c'.e y ∈ S := ⟨c'.e.map_source hyc, by show c'.e.symm (c'.e y) ∈ ptsIn X.str (σ.comp e.toRingHom) W; rw [c'.e.left_inv hyc]; exact hyW⟩
  have hSn : ∀ᶠ u in 𝓝 (c'.e y), u ∈ S := hSo.mem_nhds hu0
  have hevd : ∀ t, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ev u t) u := by
    intro t
    filter_upwards [hSn] with u hu
    refine ((c'.holo W t).differentiableAt (hSo.mem_nhds hu)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hu] with v hv
    simp only [Function.comp_apply, hev v hv.2, ev_eq hv.2]
  have hφ : ∀ᶠ u in 𝓝 (c'.e y), (ev u).comp φ = σ := by
    filter_upwards [hSn] with u hu
    rw [hev u hu.2]; exact (hnear _ hu.2).1
  have hpt : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z =
      spMap (ev u) ≫ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι T.Z := by
    filter_upwards [hSn, hF] with u hu ⟨h, hc⟩
    refine ⟨h, ?_⟩
    rw [hc, hev u hu.2]
    have := GlobalTheory.Points.specMap_valMap_fromSpec hW (c'.e.symm u).1 hu.2
    show (c'.e.symm u).1 ≫ j ≫ genι T.Z = _
    rw [← this]
    simp only [Category.assoc]
    rfl
  obtain ⟨M, hMd, hMc⟩ := _root_.GlobalTheory.HolCoordEv.coords_holomorphic E H Dw l Xo c O β T.Z σ U hσ hU X.dim (c'.e y) Γ(X.X, W) φ _ fW ev kU G τ.1 hevd hG hφ hpt
  refine ⟨M, hMd, ?_, ?_⟩
  · obtain ⟨h0, hc0⟩ := hMc.self_of_nhds
    obtain ⟨h0', hF0⟩ := hF.self_of_nhds
    obtain ⟨-, g0, -, hm0⟩ := hnear _ hu0.2
    have hx : (cxOf e σ hj (c'.e.symm (c'.e y))).1 ≫ genι T.Z = (cxPt T.Z (U.un kU ⟨G (c'.e y), h0⟩)).1 ≫ genι T.Z := by
      rw [hF0]
    have key : ∀ {x x' : Sp ℂ ⟶ T.Z.X} (hx : x = x') (g : EigFrame T.Z σ x) (G' : EigFrame T.Z σ x')
        (N : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ),
        (∀ i, IsCombAtG T.Z.t x' (G'.v τ.1) (fun b => N b i) (g.v τ.1 i)) → IsUnit N.det := by
      intro x x' hx g G' N h
      subst hx
      rw [← EigFrame.co_eq (f := G') (g := g) h]
      exact EigFrame.isUnit_det_co _ _ _
    refine key hx g0 (cxFrame T.Z (U.un kU ⟨G (c'.e y), h0⟩)) (M (c'.e y)) fun i => ?_
    rw [hm0 τ.1 i, ← hev _ hu0.2]
    exact hc0 i
  · filter_upwards [hMc, hSn] with u ⟨h, hc⟩ hu
    obtain ⟨-, g0, hg0, hm0⟩ := hnear _ hu.2
    refine ⟨h, ⟨g0, hg0⟩, fun x g hg i => ?_⟩
    rw [_root_.GlobalTheory.LieBase.frameAt_v_eq E H Dw l Xo c O β T.Z F e σ X j f₀ A₀ A _ _ _ g g0 hg hg0 τ.1 i, hm0 τ.1 i, ← hev _ hu.2]
    exact hc i

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloFrameChart
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.LieBase.HoloFrame

theorem exists_un : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (y : CxPts (genStr T.Z) σ), ¬ LiesIn y (genBd T.Z) → ∃ (k : U.Comp) (x : (U.X k).dom), cxPt T.Z (U.un k x) = y := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ r U hU y hy
  have hr : Set.range y.1 ⊆ Set.range T.Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact not_not.1 hy
  haveI := T.Z.jQ_open
  let xF := IsOpenImmersion.lift T.Z.jQ y.1 hr
  have hxF : xF ≫ T.Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    have h2 := y.2
    rw [← hxF, Category.assoc, T.Z.jQ_over] at h2
    exact h2
  have hover : (xF ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs]
    exact GlobalTheory.ShFam.OpenReg.spMap_comp _ _
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ Limits.pullback.fst _ _ :=
    GlobalTheory.FlagTan.exists_frPt _ hover
  obtain ⟨k, f, t, hb⟩ := hU.2.2.1 z
  refine ⟨k, f, ?_⟩
  rw [cxPt_congr hb.1.symm]
  refine Subtype.ext ?_
  show GlobalTheory.AllWt.ptF (S := CAt σ) z ≫ T.Z.jQ = y.1
  rw [← hxF]
  congr 1
  apply Limits.pullback.hom_ext
  · exact (ptF_fst z).trans hz
  · exact (ptF_snd z).trans hs.symm

theorem exists_holo_frame_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k : U.Comp) (Fr : V X.dim → Frame (U.X k).Ψ (Dw.p + Dw.q)), ∀ᶠ u in 𝓝 (c'.e y), ∃ h : Fr u ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨Fr u, h⟩) = cxOf e σ hj (c'.e.symm u) ∧ ∀ τ' a b, DifferentiableAt ℂ (fun u => mat (Fr u) τ' a b) u := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hjo hj y hy c' hyc
  have hnb : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro h
    have h1 : IsLocalRing.closedPoint ℂ ∈ y.1 ⁻¹ᵁ openPart j := hy (Set.mem_univ _)
    exact h1 h
  obtain ⟨k, x₀, hx₀⟩ := exists_un E H Dw l Xo c O β Y T σ _ U hU _ hnb
  have hn := _root_.GlobalTheory.OpenBaseDim.dim_eq E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj ⟨y, hy⟩ k
  obtain ⟨W, a, ψ, hWo, haW, hψd, hψh, hψa, hinj⟩ := _root_.GlobalTheory.UnifSlice.exists_slice E H Dw l Xo c σ U hσ hU k x₀ X.dim hn
  obtain ⟨q, hOo, hq, hqd⟩ := _root_.GlobalTheory.LieBase.isHol_chart_framePt E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj c' k X.dim W ψ hWo hψd hψh
  haveI := T.Z.jQ_open
  have hxeq : ∀ {z z' : FrPt Xo c (CAt σ)}, cxPt T.Z z = cxPt T.Z z' → z.x = z'.x := by
    intro z z' h
    have h1 : GlobalTheory.AllWt.ptF (S := CAt σ) z = GlobalTheory.AllWt.ptF (S := CAt σ) z' :=
      (cancel_mono T.Z.jQ).1 (congrArg Subtype.val h)
    rw [← ptF_fst z, h1, ptF_fst]
  have hcxinj : Function.Injective (cxOf e σ hj) := by
    intro y1 y2 h
    apply Subtype.ext
    exact (cancel_mono j).1 (congrArg Subtype.val h)
  have hya : cxOf e σ hj y = cxPt T.Z (U.un k ⟨ψ a, hψd a haW⟩) := hx₀.symm.trans (cxPt_congr (hψa _).symm)
  have haO : a ∈ {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := ⟨haW, hψd a haW, y, hyc, hya⟩
  have hqa : q a = y := hcxinj ((hq a haW _ ⟨y, hyc, hya⟩).2.trans hya.symm)
  have hinjg : Set.InjOn (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
    rintro w ⟨hw, hwd, hw'⟩ w' ⟨hw2, hwd', hw2'⟩ hg
    have h1 := hq w hw hwd hw'
    have h2 := hq w' hw2 hwd' hw2'
    have hqq : q w = q w' := c'.e.injOn h1.1 h2.1 hg
    refine hinj w hw w' hw2 hwd hwd' (hxeq ?_)
    rw [← h1.2, ← h2.2, hqq]
  obtain ⟨h, hev⟩ := _root_.GlobalTheory.InjHol.exists_local_inverse_of_injOn X.dim _ _ a hOo haO hqd hinjg
  refine ⟨k, fun u => ψ (h u), ?_⟩
  rw [show c'.e y = c'.e (q a) by rw [hqa]]
  filter_upwards [hev] with u ⟨⟨huW, hud, hux⟩, hgu, hdu⟩
  refine ⟨hψd _ huW, ?_, fun τ' i i' => ?_⟩
  · have h1 := hq _ huW (hψd _ huW) hux
    rw [← h1.2]
    congr 1
    exact (c'.e.left_inv h1.1).symm.trans (congrArg c'.e.symm hgu)
  · exact ((hψh τ' i i' _ huW).differentiableAt (hWo.mem_nhds huW)).comp u hdu

end GlobalTheory.LieBase.HoloFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicEigenFrameDirsInExpChart
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartFrames


open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier in
theorem exists_frameFam {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (σ : c.F →+* ℂ)
    {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)} {ex : ExpMaps Z σ g} (hex : IsExpChart e ex)
    (y₀ : CxPts (genStr Z) σ) (hy₀ : y₀ ∈ e.source) :
    ∃ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (B : Set (Fin n → ℂ)) (a : (Fin n → ℂ) → CxFr Z σ), LogKS.chart V ≫ genStr Z = spMap φ ∧ IsOpen B ∧ e y₀ ∈ B ∧
      B ⊆ e.target ∧ HolFam B a ∧
      ∀ b ∈ B, (a b).1 = e.symm b ∧ ∃ hy : (a b).1 ∈ ptsIn (genStr Z) σ V.1, (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (evHom hy) (a b).2 := by
  obtain ⟨U, hU, φ, F, hzU, hφ, -⟩ :=
    EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (y₀.1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hy₀V : y₀ ∈ ptsIn (genStr Z) σ V.1 := CxPts.mem_ptsIn.2 hzU
  have hov : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), σ = (evHom hy).comp φ := fun y hy =>
    EigLoc.spMap_inj (y.2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, spMap_evHom hy]))
  have hx : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom hy) ≫ LogKS.chart V ≫ genι Z := fun y hy => by
    rw [← Category.assoc, spMap_evHom hy]
  have hfr : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), (fun srcFrame mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v srcFrame embτ basisIdx) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (evHom hy) f :=
    fun y hy => EigFrame.exists_isMap F (evHom hy) (hov y hy) (hx y hy)
  choose fr hfr using hfr
  have h0 : e.symm (e y₀) ∈ ptsIn (genStr Z) σ V.1 := by rw [e.left_inv hy₀]; exact hy₀V
  let a : (Fin n → ℂ) → CxFr Z σ := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then ⟨e.symm b, fr _ h⟩ else ⟨e.symm (e y₀), fr _ h0⟩
  have ha : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), a b = ⟨e.symm b, fr _ h⟩ := fun b h => dif_pos h
  let B : Set (Fin n → ℂ) := e.target ∩ e.symm ⁻¹' ptsIn (genStr Z) σ V.1
  have hB : IsOpen B := e.continuousOn_symm.isOpen_inter_preimage e.open_target (isOpen_ptsIn _)
  have hBt : B ⊆ e.target := Set.inter_subset_left
  have hyB : IsHolTo B (fun b => (e.symm b).1) := LocLift.isHolTo_mono hex.2.2.1 hB hBt
  let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then evHom h else evHom h0
  have hev : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), ev b = evHom h := fun b h => dif_pos h
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hd : ∀ r : Γ(gen Z, V.1), DifferentiableOn ℂ (fun b => ev b r) B := fun r b hb =>
    (HolLieFrame.differentiableAt_ev hyB (LogKS.chart V) ev
      (fun b' hb' => by rw [hev b' hb'.2]; exact (spMap_evHom hb'.2).symm) hb r).differentiableWithinAt
  refine ⟨V, φ, F, B, a, hφ', hB, ⟨e.map_source hy₀, h0⟩, hBt, ⟨?_, fun ρ i => ?_⟩, fun b hb => ?_⟩
  · exact LocLift.isHolTo_congr hyB fun b hb => by rw [ha b hb.2]
  · exact HolFrames.holTan_dualMap hB (F.v ρ i) (fun b hb => evHom hb.2)
      (fun r => ⟨fun b => ev b r, hd r, fun b hb => (RingHom.congr_fun (hev b hb.2) r).symm⟩)
      (fun b hb => by rw [ha b hb.2]; exact hfr _ hb.2 ρ i)
  · rw [ha b hb.2]
    exact ⟨rfl, hb.2, hfr _ hb.2⟩


open GlobalTheory.Cartier in
theorem exists_open_mem {F : Type} [Field F] (X : Var F) {κ : Type} [Finite κ] {m : κ → ℕ} (S : Fr (ratOf X) m 0)
    {p : X.X} {A : Mat m X.Fn} (hA : A ∈ S.S p) : ∃ G : X.X.Opens, p ∈ G ∧ ∀ p' ∈ G, A ∈ S.S p' := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc p
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt p g → ∃ W : X.X.Opens, p ∈ W ∧ ∀ p' ∈ W, RegAt p' g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    exact ⟨W, hW, fun p' hp' => regAt_fnOf hp' _ a⟩
  choose W hW hW' using fun (τ : κ) (i j : Fin (m τ)) => hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))
  choose W₂ hW₂ hW₂' using fun τ : κ => hreg _ (mem_O_ratOf.1 (hP τ).2.2.1)
  let G : Set X.X := ((show X.X.Opens from U) : Set X.X) ∩ (⋂ τ, ⋂ i, ⋂ j, (W τ i j : Set X.X)) ∩ ⋂ τ, (W₂ τ : Set X.X)
  have hG : IsOpen G := (U.isOpen.inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (W τ i j).isOpen)).inter (isOpen_iInter_of_finite fun τ => (W₂ τ).isOpen)
  refine ⟨⟨G, hG⟩, ⟨⟨hU, Set.mem_iInter.2 fun τ => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hW τ i j⟩,
    Set.mem_iInter.2 fun τ => hW₂ τ⟩, fun p' hp' => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp'
  exact (hS _ h1 A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 (hW' τ i j p'
      (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 h2 τ) i) j)), (hP τ).2.1,
    mem_O_ratOf.2 (hW₂' τ p' (Set.mem_iInter.1 h3 τ)), fun i j hi => absurd hi (by simp)⟩

theorem valR_appIso_inv {Y X : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (W : Y.Opens) (g : Γ(Y, W))
    (w : Sp ℂ ⟶ Y) (hw : ⊤ ≤ w ⁻¹ᵁ W) :
    valR (w ≫ j) (j ''ᵁ W) ((j.appIso W).inv.hom g) = valR w W g := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  rw [← GlobalTheory.Points.valR_appLE w j hle hw, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact GlobalTheory.Points.valR_res w le_rfl hw g

end GlobalTheory.LieBase.ChartFrames

namespace GlobalTheory.LieBase.ChartFrames

open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier

theorem cxOf_mem_image {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z} [IsOpenImmersion j]
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)) :
    cxOf e σ hj z ∈ ptsIn (genStr Z) σ (j ''ᵁ W) ↔ z ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  show j (z.1 (IsLocalRing.closedPoint ℂ)) ∈ j ''ᵁ W ↔ _
  exact ⟨fun ⟨x, hx, hxe⟩ => (j.isOpenEmbedding.injective hxe) ▸ hx, fun h => ⟨_, h, rfl⟩⟩

end GlobalTheory.LieBase.ChartFrames


open GlobalTheory GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.LieBase.ChartFrames in
theorem GlobalTheory.LieBase.exists_chart_dirs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (C : FlagCpt T.Z e) (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ r : ℝ, 0 < r ∧ ∃ W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ, (∀ p k, DifferentiableOn ℂ (fun u => W u p k) (Metric.ball 0 r)) ∧ LinearIndependent ℂ (W 0) ∧ ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source → ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r → (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧ ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' → Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ C X j f f₀ Eb A₀ hj hL y n g ch₀ ex hex hys hy0
  obtain ⟨hoi, -, hT⟩ := hL
  obtain ⟨A, hA⟩ := Eb.nonempty (GlobalTheory.Cartier.under y)
  obtain ⟨V, φ, Φ, B, a, hφ, hB, h0B, hBt, ha, hab⟩ := exists_frameFam T.Z σ hex (cxOf e σ hj y) hys
  rw [hy0] at h0B
  have hsy : ch₀.symm 0 = cxOf e σ hj y := by rw [← hy0]; exact ch₀.left_inv hys
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := by
    obtain ⟨h1, hy, -⟩ := hab 0 h0B
    rwa [h1, hsy] at hy
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.LieBase.coords_eq_ratVal_of_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ A
  have hMy := hM y hA hyV
  choose Ws hWs s hs using fun τ p q => (hMy.1 τ p q).exists_fnOf
  obtain ⟨G, hG, hGA⟩ := exists_open_mem X Eb hA

  have hoi' : IsOpenImmersion j := hoi
  let sv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → (Fin n → ℂ) → ℂ := fun τ p q u =>
    valAt' (ch₀.symm u).1 (j ''ᵁ Ws τ p q) ((j.appIso (Ws τ p q)).inv.hom (s τ p q))
  let Ω : Set (Fin n → ℂ) := B ∩ (ch₀.target ∩ ch₀.symm ⁻¹' (ptsIn (genStr T.Z) σ (j ''ᵁ G) ∩
    ⋂ τ, ⋂ p, ⋂ q, ptsIn (genStr T.Z) σ (j ''ᵁ Ws τ p q)))
  have hΩ : IsOpen Ω := hB.inter (ch₀.continuousOn_symm.isOpen_inter_preimage ch₀.open_target
    ((isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun p =>
      isOpen_iInter_of_finite fun q => isOpen_ptsIn _)))
  have h0Ω : (0 : Fin n → ℂ) ∈ Ω := by
    refine ⟨h0B, hBt h0B, ?_⟩
    rw [Set.mem_preimage, hsy]
    exact ⟨(cxOf_mem_image e σ hj G y).2 (CxPts.mem_ptsIn.2 hG), Set.mem_iInter.2 fun τ => Set.mem_iInter.2 fun p =>
      Set.mem_iInter.2 fun q => (cxOf_mem_image e σ hj _ y).2 (CxPts.mem_ptsIn.2 (hWs τ p q))⟩
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ 0 h0Ω
  have src : ∀ b ∈ B, (a b).1 ∈ ch₀.source := fun b hb => by
    rw [(hab b hb).1]; exact ch₀.map_target (hBt hb)
  have h5 := fun b (hb : b ∈ B) => hex.2.2.2.2.2 _ (src b hb)
  choose! Wa hWa using fun b (hb : b ∈ B) (z : Pad.Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hWad : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => Wa b z) b := fun b hb z =>
    ExpDirs.differentiableAt_dir hex hB ha.1 src (ha.2 z.1 z.2) (fun b hb => hWa b hb z) hb
  have hsvd : ∀ τ p q, ∀ u ∈ Ω, DifferentiableAt ℂ (sv τ p q) u := fun τ p q u hu => by
    have h := hex.2.2.1 (j ''ᵁ Ws τ p q) ((j.appIso (Ws τ p q)).inv.hom (s τ p q))
    refine h.2.differentiableAt (h.1.mem_nhds ⟨hu.2.1, ?_⟩)
    exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hu.2.2.2 τ) p) q
  let W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ := fun u p k =>
    ∑ q, sv p.1 q p.2 u * Wa u ⟨p.1, q⟩ k
  have evEq : ∀ {y₁ y₂ : CxPts (genStr T.Z) σ} (h₁ : y₁ ∈ ptsIn (genStr T.Z) σ V.1)
      (h₂ : y₂ ∈ ptsIn (genStr T.Z) σ V.1), y₁ = y₂ → evHom h₁ = evHom h₂ := by
    rintro _ _ _ _ rfl; rfl
  have key : ∀ z : CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source →
      ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r →
      (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧
      ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' →
        Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
    intro z hzs hzr
    have huΩ := hrΩ hzr
    have hsymm : ch₀.symm (ch₀ (cxOf e σ hj z)) = cxOf e σ hj z := ch₀.left_inv hzs
    obtain ⟨huB, -, hu1, hu2⟩ := huΩ
    rw [hsymm] at hu1 hu2
    have hzG := (cxOf_mem_image e σ hj G z).1 hu1
    have hzW : ∀ τ p q, z ∈ ptsIn X.str (σ.comp e.toRingHom) (Ws τ p q) := fun τ p q =>
      (cxOf_mem_image e σ hj _ z).1 (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hu2 τ) p) q)
    have hAz : A ∈ Eb.S (GlobalTheory.Cartier.under z) := hGA _ (CxPts.mem_ptsIn.1 hzG)
    obtain ⟨ha1, hyV', hmap⟩ := hab _ huB
    have hzV : cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by rw [← hsymm, ← ha1]; exact hyV'
    obtain ⟨-, hex', hco⟩ := hM z hAz hzV
    refine ⟨hex', fun g' hg' => ?_⟩
    have hov : σ = (evHom hzV).comp φ := EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ, ← Category.assoc, spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, spMap_evHom hzV]
    obtain ⟨fr, hfr⟩ := Φ.exists_isMap (evHom hzV) hov hx
    have hcoM := hco g' hg' fr hfr
    have hpt : (a (ch₀ (cxOf e σ hj z))).1 = cxOf e σ hj z := ha1.trans hsymm
    have hvq : ∀ τ i, fr.v τ i = (a (ch₀ (cxOf e σ hj z))).2.v τ i := fun τ i => by
      rw [hfr τ i, hmap τ i, evEq hzV hyV' hpt.symm]
    have hD : ∀ q : Pad.Letter Dw, IsDerivAt0 (fun w => (ex (cxOf e σ hj z) w).left)
        (Wa (ch₀ (cxOf e σ hj z)) q) (fr.v q.1 q.2) := fun q => by
      have tr : ∀ (x x' : CxPts (genStr T.Z) σ), x = x' → ∀ w v,
          IsDerivAt0 (fun u => (ex x u).left) w v → IsDerivAt0 (fun u => (ex x' u).left) w v := by
        rintro _ _ rfl _ _ h; exact h
      rw [hvq]
      exact tr _ _ hpt _ _ (hWa _ huB q)
    have e0 : ex (cxOf e σ hj z) 0 = 1 := by simpa using hex.2.2.2.1 _ hzs 0 0
    rintro ⟨τ, i⟩
    have hcomb := ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e0) (fun k => fr.tan τ k) (fun k => hD ⟨τ, k⟩)
      (g'.tan τ i) (fr.co_spec g' τ i)
    convert hcomb using 1
    funext k
    simp only [W, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [hcoM τ, Matrix.map_apply, ← hs τ q i, ratVal_fnOf (hzW τ q i)]
    show valR (ch₀.symm (ch₀ (cxOf e σ hj z))).1 _ _ = _
    rw [hsymm]
    exact valR_appIso_inv j _ _ z.1 (hzW τ q i)
  refine ⟨A, hA, r, hr, W, fun p k u hu => ?_, ?_, key⟩
  · have huΩ := hrΩ hu
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [W]
    refine DifferentiableAt.fun_sum fun q _ => (hsvd _ _ _ u huΩ).mul ?_
    exact differentiableAt_pi.1 (hWad u huΩ.1 ⟨p.1, q⟩) k
  · obtain ⟨⟨g', hg'⟩, hall⟩ := key y hys (by rw [hy0]; exact Metric.mem_ball_self hr)
    have hD := hall g' hg'
    rw [hy0] at hD
    have e0 : ex (cxOf e σ hj y) 0 = 1 := by simpa using hex.2.2.2.1 _ hys 0 0
    have h5y := hex.2.2.2.2.2 _ hys
    obtain ⟨bs, hbs⟩ := ExpDirs.dirs_basis g' (e := fun w => (ex (cxOf e σ hj y) w).left) (congrArg (·.left) e0)
      h5y.1 h5y.2 hD
    rw [← hbs]
    exact bs.linearIndependent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superadditive_of_cells_cover_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone (bar := bar) (X := X), ∀ B' ∈ psdCone (bar := bar) (X := X), evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  first | exact @GlobalTheory.PolFan.CoverSuper.superadd_of_cover | exact GlobalTheory.PolFan.CoverSuper.superadd_of_cover | (intros; apply GlobalTheory.PolFan.CoverSuper.superadd_of_cover <;> assumption)
end

