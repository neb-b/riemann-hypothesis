module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0219
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0221
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeIsometryTransport
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeConjugateCusp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverField
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowlaSelbergPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_curve0_hasPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) →
    ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧
      (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro E _ _ _ H _ χ hχ ρ hρ
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hU := GlobalTheory.thetaUnifAV_closed
  have hX := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  obtain ⟨M, _, ω, C, x, hω, hpr, hper, hx⟩ := _root_.GlobalTheory.CM.EllExists.exists_ell _root_.GlobalTheory.cmCurve_closed hU hL hX E H χ hχ ρ hρ
  obtain ⟨C', π, c'⟩ := exists_ellMap hL.polBaseChange E H _ ω C ℂ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P π c'.2.1 u
  obtain ⟨Hm, χ', Ef, h1, h2, h3⟩ := id hu
  obtain ⟨w, hw, -⟩ := h2 C'.v (C'.basis.1 0)
  have hd := C'.dim
  let Z : Curve0 H ρ := ⟨M, ω, C, hω, C', π, c', u, hu, c, hc, hΛ, w ⟨0, by omega⟩ / c, by
    convert hw using 1
    funext j
    rw [mul_div_cancel₀ _ hc]
    congr 1
    apply Fin.ext
    have := j.2
    simp only
    omega⟩
  exact ⟨Z, x, _root_.GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H ρ Z, hper, hx⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem mem_Vgen (𝔐 : HodgeCpt Y S₀ Dc.y) (t : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ) {x : 𝔐.Li}
    (hx : x ∈ 𝔐.V t p) : x ∈ 𝔐.Vgen t := by
  obtain ⟨U, hU, b, hs, hf⟩ := 𝔐.vb t p trivial
  have e : 𝔐.V t p = Submodule.span (regAt 𝔐.ξ p) (Set.range b) := (hf p trivial hU).2
  have hx' : x ∈ Submodule.span (regAt 𝔐.ξ p) (Set.range b) := e ▸ hx
  clear hx
  show x ∈ 𝔐.Vgen t
  have hs' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t := hs
  rw [← hs']
  induction hx' using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span h
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | smul a x _ h => exact Submodule.smul_mem _ (a : Ω) h

theorem disjoint_blocks (Or : CptOrigin Y S₀ Dc Hd) (τ : CMType H) :
    Disjoint (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) := by
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c _ _ Y S₀ Ω K J Dc.y Or.𝔐
    (FaithfulSMul.algebraMap_injective _ _)
  exact hind.pairwiseDisjoint (Or.bg_ne_sm τ τ)

theorem exists_smallPart (Or : CptOrigin Y S₀ Dc Hd) {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) :
    ∃ s, Or.IsSmallPart d s := by
  have h : ∀ τ k, ∃ x, x ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - x ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have hm : Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 hm
    exact ⟨e, he, by rw [← hae]; simpa using ha⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem frames (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (d : MuFrameAt Hd w) {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li}
    (hs : Or.IsSmallPart d s) (τ : CMType H) (h : genPt Or.𝔐.ξ ⤳ centre z) :
    (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt (d.b τ) ⟨centre z, h⟩ ∧
    (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩ ∧
    ∀ k, Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩ := by
  have hfr := _root_.GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ d.c d.f (d.b τ) h hw (d.adapted τ).1 d.inDom
  have hb := _root_.GlobalTheory.CompanionTheory.Ar.BlockFrame.frame_of_sum_frame Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
    (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (d.b τ) (s τ) ⟨centre z, h⟩ (Or.i_inj τ)
    (Or.i_range τ) (disjoint_blocks Or τ) (fun _ hx => mem_Vgen _ _ _ hx) (fun _ hx => mem_Vgen _ _ _ hx) hfr
    (by rw [(d.adapted τ).2.2, Or.F_eq τ]) (hs τ)
  exact ⟨hfr, hb.1, hb.2.1⟩

theorem norm_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s) :
    ∃ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) ∧ (∀ τ, (Γ τ).PosDef) ∧
      d.norm = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have key : ∀ τ, ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ,
      Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) Γ ∧ Γ.PosDef ∧
        quotNormSq Dc.j_le_N (gramAt (Dc.h τ) (d.b τ) w) = Γ.det.re := fun τ => by
    obtain ⟨h1, h2, h3⟩ := frames Or hw d hs τ h
    obtain ⟨G, hG, hGp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) h hi h1
    rw [_root_.GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen.gramAt_eq_hodge E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ (d.b τ) h G hw hi h1 hG]
    exact _root_.GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z τ (d.b τ) (s τ) h G hi h1
      ((d.adapted τ).2.2) (fun k => (hs τ k).1) h3 h2 hG hGp
  choose Γ h1 h2 h3 using key
  refine ⟨Γ, h1, h2, ?_⟩
  unfold MuFrameAt.norm
  simp_rw [h3]

theorem det_re_pos {n : ℕ} {Γ : Matrix (Fin n) (Fin n) ℂ} (h : Γ.PosDef) : 0 < Γ.det.re :=
  (Complex.pos_iff.1 h.det_pos).1

theorem phMu_eq (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hi : Or.𝔐.Interior z) (d : MuFrameAt Hd w)
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs : Or.IsSmallPart d s)
    {Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ}
    (hΓ : ∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) :
    phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) +
      (∑ τ, Real.log (Γ τ).det.re) / 2 := by
  have h : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  haveI : CharZero Ω := algebraRat.charZero Ω
  have htie : CoordTie ℤ Or.𝔐.ξ (fun c' : (k : K) → J k => ∏ k, Dc.y ⟨k, c' k⟩) := Or.𝔐.tie
  have hpol := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  obtain ⟨cv, hcv, hwc⟩ := exists_eq_smul_orbitRep w
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = orbitRep w := ⟨_, rfl⟩
  rw [← hw₀def] at hwc
  have hwk : ∀ p, w p = cv p.1 * w₀ p := fun p => congrFun hwc p
  have hw₀ : CoordsAt Or.𝔐.ξ Dc.y z w₀ := by
    have := RootHt.ArchB.coordsAt_smul (fun k => (cv k)⁻¹) (fun k => inv_ne_zero (hcv k)) hw
    convert this using 1
    funext p
    rw [hwc]
    simp [torusSmul, inv_mul_cancel_left₀ (hcv p.1)]
  have hval : ∀ (a : Ω) (v : ℂ), IsValueAt Dc.y a w v ↔ IsValueAt Dc.y a w₀ v := fun a v =>
    ((_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw a v).symm).trans
      (_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w₀ h hw₀ a v)
  have hne₀ : ∀ k, w₀ ⟨k, d.c k⟩ ≠ 0 := fun k h0 => d.inDom.1 k (by rw [hwk ⟨k, d.c k⟩]; simp [h0])
  let d₁ : MuFrameAt Hd w₀ :=
    { c := d.c, f := d.f
      inDom := ⟨hne₀, d.inDom.2.imp fun v hv => ⟨(hval _ _).1 hv.1, hv.2⟩⟩
      b := d.b, adapted := d.adapted, u := d.u, unit := d.unit, eq := d.eq }
  have hs₁ : Or.IsSmallPart d₁ s := hs
  have hu := _root_.GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie h hw d.inDom d.unit
  have hmc₀ : w₀ ∈ mcPts (mCoordIdeal Dc.y) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie w₀).2 ⟨z, h, hw₀⟩
  have hu₀ : valAt Dc.y d.u w₀ = valAt Dc.y d.u w :=
    valAt_eq hmc₀ ((hval _ _).1 ((_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y htie z w h hw _ _).1 hu.2))

  have hne := _root_.GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hw₀
  obtain ⟨s₀, hs₀⟩ := exists_smallPart Or hne.some
  obtain ⟨Γ₀, g₀, p₀, n₀⟩ := norm_eq Or hw₀ hi hne.some hs₀
  obtain ⟨Γ₁, g₁, p₁, -⟩ := norm_eq Or hw₀ hi d₁ hs₁
  have e₁ : Γ₁ = Γ := funext fun τ =>
    _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z _ (s τ) _ _ hpol (g₁ τ) (hΓ τ)
  subst e₁
  have hind := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w₀ hne.some d₁ s₀ s Γ₀ Γ₁ hw₀ hi hs₀ hs₁ g₀ g₁ p₀
  have hF : muMetric Hd w₀ = ‖valAt Dc.y d.u w‖ * (∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    unfold muMetric
    rw [dite_eq_left hne, n₀, hind]
    show ‖valAt Dc.y d.u w₀‖ * _ * _ = _
    rw [hu₀]
  have hA : 0 < ‖valAt Dc.y d.u w‖ := norm_pos_iff.2 hu.1
  have hsq : 0 < ∏ τ, Real.sqrt (Γ₁ τ).det.re :=
    Finset.prod_pos fun τ _ => Real.sqrt_pos.2 (det_re_pos (p₁ τ))
  have hprod₀ : 0 < ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hne₀ k)) _
  have hprod : 0 < ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _
  have hpos : 0 < muMetric Hd w₀ := by
    rw [hF]
    positivity
  have hnz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => ⟨d.c k, d.inDom.1 k⟩
  have hh : (muLine Hd).h w = (∏ k, ‖cv k‖ ^ Hd.aMu k) * muMetric Hd w₀ := by
    subst hw₀def
    exact TopNPoly.hermOfFun_h_smul hcv hwc hnz hpos
  have hcw : (∏ k, ‖cv k‖ ^ Hd.aMu k) * ∏ k, ‖w₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k = ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← norm_mul]
    rw [hwk ⟨k, d.c k⟩]
  have hfin : (muLine Hd).h w = (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
      ∏ τ, Real.sqrt (Γ₁ τ).det.re := by
    rw [hh, hF, ← hcw]
    ring
  show Real.log ((muLine Hd).h w) = _
  rw [hfin, Real.log_mul (by positivity) hsq.ne', Real.log_prod (fun τ _ => (Real.sqrt_pos.2 (det_re_pos (p₁ τ))).ne')]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun τ _ => Real.log_sqrt (det_re_pos (p₁ τ)).le

theorem phMu_small : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  intro _ E _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hw
  have htie : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  refine ⟨_root_.GlobalTheory.CompanionTheory.Ar.MuFrame.nonempty_muFrameAt E H D l (Xo l) c Y II K J Ω W Dc Hd S₀ Or z w hw, fun d => ⟨exists_smallPart Or d, fun s hs => ⟨
    fun τ h => (frames Or hw d hs τ h).2.1, ?_, fun hi Γ hΓ => phMu_eq Or hw hi d hs hΓ⟩⟩⟩
  exact (_root_.GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w d.c d.f d.u htie (Or.𝔐.all _) hw d.inDom d.unit).1

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

open GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

def IsWeightAt (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (x : ℝ) : Prop :=
  ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (σ : CMType H → (𝓞 E →+* ℂ)),
    FibreLat Or.𝔐.t z R ∧ Or.𝔐.LabVal z Or.sm σ ∧ x = R.cuspW σ

theorem IsWeightAt.unique {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x x' : ℝ} (h : IsWeightAt Or z x)
    (h' : IsWeightAt Or z x') : x = x' := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨g', Λ', i₃, i₄, R', σ', hF', hL', rfl⟩ := h'
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  exact (_root_.LevelTowerAlt.riemann_lattice_isometry_transport E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm ▸ rfl

theorem IsWeightAt.nonneg {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) : 0 ≤ x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, -, -, rfl⟩ := h
  exact le_max_left _ _

theorem exists_isWeightAt (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} (hz : Or.𝔐.Interior z) :
    ∃ x, IsWeightAt Or z x := by
  have hpq : 1 ≤ D.p + D.q := by
    have := Dc.two_le_N
    rw [Or.N_eq] at this
    omega
  obtain ⟨g, Λ, i₁, i₂, R, x, hF, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior hG.2.2.2.2.1 E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z hpq hz hG
    Empty (fun i => i.elim) (fun i => i.elim)
  obtain ⟨σ₀, h0, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hx : x = fun i => i.elim := funext fun i => i.elim
  subst hx
  exact ⟨_, g, Λ, i₁, i₂, R, fun τ => σ₀ (Or.sm τ), hF, fun τ a => h0 (Or.sm τ) a, rfl⟩

theorem IsWeightAt.conj {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) :
    IsWeightAt Or (spMap (starRingEnd ℂ) ≫ z) x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨-, R', hP, hH, hB, hW⟩ := _root_.LevelTowerAlt.riemann_lattice_conjugate_cusp E g Λ (CMType H) R σ (isCMFam_of_labVal Or hL)
  have hF' : FibreLat Or.𝔐.t (spMap (starRingEnd ℂ) ≫ z) R' :=
    (GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move E H Or.𝔐.X Or.𝔐.X Or.𝔐.t Or.𝔐.t (𝟙 _) g Λ R R' z).2 hP hH
      (fun a x => by simpa using hB a (star x)) hF
  exact ⟨g, Λ, i₁, i₂, R', fun τ => (starRingEnd ℂ).comp (σ τ), hF',
    fun τ a => GlobalTheory.CompanionTheory.Ar.HodgeLine.valAt_conj (hL τ a), hW.symm⟩

def HasWeight (Or : CptOrigin Y S₀ Dc Hd) (w : (Σ k, J k) → ℂ) (x : ℝ) : Prop :=
  ∃ z : Sp ℂ ⟶ Or.𝔐.X, CoordsAt Or.𝔐.ξ Dc.y z w ∧ Or.𝔐.Interior z ∧ IsWeightAt Or z x

theorem HasWeight.unique {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x x' : ℝ} (h : HasWeight Or w x)
    (h' : HasWeight Or w x') : x = x' := by
  obtain ⟨z, hz, -, hx⟩ := h
  obtain ⟨z', hz', -, hx'⟩ := h'
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt _ _ _ K J Dc.y Or.𝔐.tie Or.𝔐.normal Or.𝔐.all z z' w hz hz'
  subst e
  exact hx.unique hx'

theorem HasWeight.torus {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) : HasWeight Or (torusSmul a w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  exact ⟨z, coordsAt_torusSmul Or.𝔐.ξ hz ha, hi, hx⟩

theorem HasWeight.conj {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) :
    HasWeight Or (conjVec w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  have hc := GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w
  refine ⟨_, hc.2 hz, ?_, hx.conj⟩
  show centre _ ∈ _
  rw [hc.1]
  exact hi

theorem exists_cuspWeight : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ w, 0 ≤ U w) ∧ (∀ w (a : K → ℂ), (∀ k, a k ≠ 0) → U (torusSmul a w) = U w) ∧ (∀ w, U (conjVec w) = U w) ∧ ∀ U', Or.𝔐.IsCuspWeight Or.sm U' → ∀ w ∈ Dc.Xo, U' w = U w := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  classical
  let U : ((Σ k, J k) → ℂ) → ℝ := fun w => if h : ∃ x, HasWeight Or w x then h.choose else 0
  have hU : ∀ {w x}, HasWeight Or w x → U w = x := fun {w x} h => by
    have hex : ∃ x, HasWeight Or w x := ⟨x, h⟩
    simp only [U, dif_pos hex]
    exact hex.choose_spec.unique h
  have hU0 : ∀ {w}, (¬ ∃ x, HasWeight Or w x) → U w = 0 := fun {w} h => by
    simp only [U, dif_neg h]
  have hw : ∀ {z : Sp ℂ ⟶ Or.𝔐.X} {w} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
      {σ : CMType H → (𝓞 E →+* ℂ)}, CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → FibreLat Or.𝔐.t z R →
      Or.𝔐.LabVal z Or.sm σ → HasWeight Or w (R.cuspW σ) := by
    intro z w g Λ i₁ i₂ R σ hz hi hF hL
    exact ⟨z, hz, hi, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩
  refine ⟨U, fun z w hz hi => ?_, fun w => ?_, fun w a ha => ?_, fun w => ?_, fun U' hU' w hX => ?_⟩
  · obtain ⟨x, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := exists_isWeightAt hG Or hi
    exact ⟨g, Λ, i₁, i₂, R, σ, hF, hL, hU (hw R hz hi hF hL)⟩
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx]
      obtain ⟨z, -, -, hz⟩ := hx
      exact hz.nonneg
    · rw [hU0 h]
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU (hx.torus ha)]
    · have h' : ¬ ∃ x, HasWeight Or (torusSmul a w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : torusSmul (fun k => (a k)⁻¹) (torusSmul a w) = w := by
          funext q
          show (a q.1)⁻¹ * (a q.1 * w q) = w q
          rw [inv_mul_cancel_left₀ (ha q.1)]
        have := hx.torus (a := fun k => (a k)⁻¹) fun k => inv_ne_zero (ha k)
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU hx.conj]
    · have h' : ¬ ∃ x, HasWeight Or (conjVec w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : conjVec (conjVec w) = w := by
          funext q
          exact Complex.conj_conj (w q)
        have := hx.conj
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · obtain ⟨z, -, hz⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hX.1
    have hi : Or.𝔐.Interior z := by
      by_contra hn
      exact hX.2 ((Or.bd z w hz).2 hn)
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU' z w hz hi
    rw [he, hU (hw R hz hi hF hL)]

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliSchemesExist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem moduli_schemes_exist : N1ab := GlobalTheory.Moduli.moduli_scheme_exists

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverFieldStatement
section
alias _root_.GlobalTheory.T.root_origin_coords_over_field :=
  GlobalTheory.CompanionTheory.Ar.root_model_on_cover
end

