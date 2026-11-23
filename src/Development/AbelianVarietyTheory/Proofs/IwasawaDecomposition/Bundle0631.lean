module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.TwInputs.PlacesAt

theorem evLgG_placesOk : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (GlobalTheory.TwInputs.SmallField.lg_lam K).imp fun B f _ hO _ _ T w Z => ?_
  have hq := GlobalTheory.TwInputs.SmallField.auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact B.toPre.host).1
  obtain ⟨w0, hw0⟩ := GlobalTheory.TwInputs.SmallField.exists_over B.toPre.host.E hqp
  have hmod : ∀ p ∈ [B.toPre.host.g 0, B.toPre.host.g 1, B.toPre.host.pde, B.toPre.host.pde', GlobalTheory.EX.DC.q0H B.toPre.host],
      p ≡ 1 [MOD B.toPre.host.QS * B.toPre.host.q * B.toPre.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (GlobalTheory.TwInputs.SmallField.one_lt_cond B.toPre)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [B.toPre.g_cond 0, B.toPre.g_cond 1, B.toPre.pde_cond.1, B.toPre.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  exact ⟨w0, (GlobalTheory.LamTie.placesOk_of_modEq_one B.toPre.R B.toPre.host _ w0 hqp hmod hq
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0).1⟩

end GlobalTheory.TwInputs.PlacesAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoices
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HypCMRec

theorem hypCM_all (D : D7) : SphericalInertData.HypCM D := by
  refine ⟨?_, GlobalTheory.DesignBC.two_le_finrank D, fun w hw h2 => hw (GlobalTheory.DesignBC.isSplitPl_of_two_mem D w h2)⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem hypCM_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) :=
  evG_all fun K => lg_all K fun _ _ _ _ _ _ _ _ => hypCM_all _

end GlobalTheory.Mem.HypCMRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrde
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem isAlgebraic_exp_two_pi_div (n : ℕ) (hn : 0 < n) :
    IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / n)) :=
  (((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top (A := ℚ)).isAlgebraic

theorem rootsLL_evLgG :
    EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  have hLg : ∀ K : Ctx, large₂ K fun B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
    intro K
    refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
      fun B _ _ _ _ => {Complex.exp (2 * Real.pi * Complex.I / B.restRowsFiniteGroupCard)}, by simp, ?_, ?_⟩
    · intro B _ _ _ _ z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      exact isAlgebraic_exp_two_pi_div _ B.restRowsFiniteGroupCard_pos
    · intro B f T₀ _ hH _ _ _ T w Z
      obtain ⟨x, hx⟩ : ∃ x : B.LL, B.embLL x = Complex.exp (2 * Real.pi * Complex.I / B.toPre.restRowsFiniteGroupCard) :=
        hH.2 _ (Finset.mem_singleton_self _)
      refine ⟨x, ?_⟩
      show IsPrimitiveRoot x B.toPre.restRowsFiniteGroupCard
      rw [← IsPrimitiveRoot.map_iff_of_injective (f := B.embLL) B.embLL.injective, hx]
      exact Complex.isPrimitiveRoot_exp _ B.toPre.restRowsFiniteGroupCard_pos.ne'
  exact EvG.imp evG_good fun K _ _ _ _ _ => hLg K

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadrat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HostEFK

theorem hypEFK_ev : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) :=
  evG_all fun K => lg_all K fun B f T _ _ T' w Z => GlobalTheory.DesignBC.hypEFK (w.D Z)

end GlobalTheory.Mem.HostEFK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.RankSize

theorem rank_ge_hundred : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r := by
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨100, fun K _ _ _ _ hx _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp_all, by simp_all,
    fun B f _ hO _ _ _ _ T w Z => ?_⟩
  show 100 ≤ B.R.r
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hRK : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hR : GlobalTheory.EX.RankVal K.s B.toPre.R := hRK ▸ K.ok.rank
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1 := K.s.one_lt_alt
  have he := K.s.eps_pos
  have hk1 : K.s.x ≤ (B.toPre.R.k : ℝ) := by
    calc K.s.x = K.s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K.s.x ^ (9 / 2 + 10 * K.s.eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      _ ≤ _ := hk
  have h100 : (100 : ℝ) ≤ (B.toPre.R.k : ℝ) := hx.trans hk1
  have hk100 : 100 ≤ B.toPre.R.k := by exact_mod_cast h100
  have h2m := B.toPre.R.two_le_m
  have hmk := B.toPre.R.m_add_three_le_k
  have hkr : B.toPre.R.k ≤ B.toPre.R.r := by unfold Ranks.r; omega
  exact hk100.trans hkr

end GlobalTheory.Mem.RankSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLieEigenspaceFrameAtUniformisation
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrame

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end SlopeTestRemainingChoices

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ} {e : F ≃+* c.F} {X : Var F} {j : X.X ⟶ gen Z}
  {f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)} {S : Fr (ratOf X) Dw.mult 0} {A₀ : Mat Dw.mult X.Fn}

theorem exists_frame_of_tied (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (y : CxPts X.str (σ.comp e.toRingHom)) {A : Mat Dw.mult X.Fn} (hA : A ∈ S.S (under y)) :
    ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g := by
  obtain ⟨φ, fz, hc⟩ := hT.2 (under y) A hA
  have hy : y.1 = spMap (Var.evStalk y) ≫ stalkPt X (under y) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm
  have hφ : σ = (Var.evStalk y).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under y)).commutes _).symm)
    show σ a = Var.evStalk y (φ a)
    rw [h3]
    refine Eq.trans ?_ ((Var.evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
    simp
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (Var.evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [hy]
    exact Category.assoc _ _ _
  obtain ⟨g, hg⟩ := fz.exists_isMap (Var.evStalk y) hφ hx
  exact ⟨g, φ, fz, Var.evStalk y, hy, hc, hg⟩

end Frame

theorem eventually_frameAt_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ᶠ w in nhds v, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU k X j f₀ Eb A₀ hj hji hT ψ hψ h v hv A hA
  classical
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) hp0 (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((GlobalTheory.TrueCx.TorHolo.differentiable_stdMat (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have key : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p),
      cxOf e σ hj (ψ v) = cxPt T.Z (U.un k (x (L v))) := by
    intro v hv
    have h1 := hψ (x (L v))
    have h2 : flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (x (L v)).1) = v := by
      show flat (domPt _ _ _ (stdFrame _ _ _ hp0 (unflat (L.symm (L v)))).1) = v
      rw [L.symm_apply_apply, domPt_stdFrame _ _ _ hp0 hv]
      rfl
    rw [h2] at h1
    exact h1
  have hcont : ContinuousOn (fun b => cxPt T.Z (U.un k (x b))) B := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun W => ⟨?_, fun g => ?_⟩
    · have := (hY W 0).1.preimage (continuous_subtype_val (p := (· ∈ B)))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : Fin _ → ℂ) ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ W} := ⟨v.2, hv⟩
      have hca := (((hY W g).2).differentiableAt (((hY W g).1).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hκ := isOpenEmbedding_cxOf e σ hj
  have hLB : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L v ∈ B := fun v hv => by
    show L.symm (L v) ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
    rwa [L.symm_apply_apply]
  have hψc : ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := by
    rw [hκ.isInducing.continuousOn_iff]
    exact (hcont.comp L.continuous.continuousOn hLB).congr fun v hv => key v hv
  have hc : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hψc.continuousAt (ho.mem_nhds hv)).comp (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  filter_upwards [hc.eventually (eventually_mem_frames hA)] with w hw
  exact exists_frame_of_tied hj hT _ hw

end GlobalTheory.UnifFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.DefSpaces

theorem v_isDefinite : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f _ hO _ T w Z j hj1 hj2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  have hm : (w.st Z).toD7.R.m = (w.D Z).R.m := rfl
  have hp := GlobalTheory.RepsObj.isPosDef_of_vStd (D := (w.st Z).toD7) ⟨j - 1, by omega⟩ (hV ⟨j - 1, by omega⟩)
  change ((w.st Z).toD7.sp.V j).IsDefinite
  intro τ
  left
  have e : j - 1 + 1 = j := by omega
  have := hp τ
  simp only [Formalism.IndefR.Links.Vc, e] at this
  exact this

end GlobalTheory.Mem.DefSpaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.Top.Bl

theorem two_mul_r_le_g_level : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ k,
    2 * (w.D Z).R.r ≤ (w.D Z).host.g k := by
  refine evG_all fun K => lg_all K fun B f T hO _ T' w Z k => ?_
  obtain ⟨sp, hT, hY, hA, hV, hz, hB, -⟩ := hO
  have hR' : B.toPre.R = K.P.R := by rw [hB]; rfl
  have hg : B.toPre.host.g = K.P.H.g := by rw [hB]; rfl
  show 2 * B.R.r ≤ B.host.g k
  rw [show B.host.g k = K.P.H.g k from congrFun hg k, show B.R.r = K.P.R.r from by rw [hR']]
  have hgk : ((K.P.R.k : ℝ) * K.s.b) ^ 8 ≤ (K.P.H.g k : ℝ) := (K.ok.val.2.2.2.2.1 k).1
  have hb : 1 ≤ K.s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [K.s.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
  have hkb : (K.P.R.k : ℝ) ^ 8 ≤ (K.P.H.g k : ℝ) :=
    le_trans (pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8) hgk
  have hk8 : (K.P.R.k) ^ 8 ≤ K.P.H.g k := by exact_mod_cast hkb
  have h2k : 2 ≤ K.P.R.k := by
    have := K.P.R.f_le_k
    have : 0 < K.P.R.ord := K.P.R.ord_pos
    omega
  have hr : 2 * K.P.R.r ≤ 4 * K.P.R.k := by
    have := K.P.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have h4 : 4 * K.P.R.k ≤ K.P.R.k ^ 8 := by
    calc 4 * K.P.R.k ≤ K.P.R.k ^ 7 * K.P.R.k := by
          apply Nat.mul_le_mul_right
          calc 4 ≤ 2 ^ 7 := by norm_num
            _ ≤ K.P.R.k ^ 7 := Nat.pow_le_pow_left h2k 7
      _ = K.P.R.k ^ 8 := by ring
  omega

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainSectionFlatCoordinates
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameLift

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ShFam.SecFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

theorem analyticAt_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) (v₀ : Tau × Fin j × Fin (r - j) → ℂ) :
    AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) v₀ := by
  have hM : ∀ c, AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) v₀ := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact analyticAt_const | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Tau × Fin j × Fin (r - j) => ℂ) _).analyticAt _
  simp only [mat_frameAt, Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.fun_mul (hM c)

end GlobalTheory.FrameLift


open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ShFam.SecFrame in
theorem GlobalTheory.FrameLift.exists_analytic_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  intro E _ _ _ p q n Xd hp h v hv
  refine ⟨fun w => frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w)), ?_, ?_, ?_⟩
  · rw [analyticAt_pi_iff]; intro τ
    rw [analyticAt_pi_iff]; intro a
    rw [analyticAt_pi_iff]; intro b
    have hL : AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v := (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v
    exact (GlobalTheory.FrameLift.analyticAt_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) τ a b
      (GlobalTheory.UnifDens.flatL h v)).comp hL
  · intro τ a b
    have e : (fun w => coW Xd (Nat.le_add_right p q)
        (frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w))) τ a b) =
        fun _ => (1 : Matrix (Fin p) (Fin p) ℂ) a b := by
      funext w; rw [(co_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) _ τ).1]
    rw [e]; exact analyticAt_const
  · have ho : IsOpen (DomFlat Xd.Ψ p (p + q - p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
    filter_upwards [(GlobalTheory.UnifDens.flatL h).continuous.continuousAt.preimage_mem_nhds (ho.mem_nhds hv)] with w hw
    refine ⟨frameAt_mem Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) hp hw, ?_⟩
    rw [domPt_frameAt]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeansStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intForm_dominating_polFanBase_classMinMeans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  first | exact @GlobalTheory.PolCell.exists_contact_baseFun_lamW | exact GlobalTheory.PolCell.exists_contact_baseFun_lamW | (intros; apply GlobalTheory.PolCell.exists_contact_baseFun_lamW <;> assumption)
end

