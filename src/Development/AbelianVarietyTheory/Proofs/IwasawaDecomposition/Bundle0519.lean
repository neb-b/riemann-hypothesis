module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up


set_option maxHeartbeats 4000000 in
theorem rows_up_at : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  let ix : w.C.Tup ≃ w.I.ι := by
    with_unfolding_all exact (Equiv.refl w.C.Tup :)
  have transported := _root_.GlobalTheory.Mem.R3.Rw.Mv.rowsAre_refill
    B w.C Z (refUp Z S' N h) w.px w.I t.hX T Wt ix p0
    (by with_unfolding_all exact (t.r :))
  rcases transported with
    ⟨⟨z', hold', Y', Z'', tup'⟩, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  subst hz
  let r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I t.hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    ⟨Mv.cpDat (refUp Z S' N h).to (refUp Z S' N h).same t.r.z, hold', Y', Z'', tup'⟩
  have eW1 := Mv.forcedContentPlaces_eq_transport_sameFiniteGroup (refUp Z S' N h).to (refUp Z S' N h).same t.r.z (F0K K.s (w.D (SRe.upL Z S' N h)))
  let t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    { hX := t.hX
      r := r'
      exAt := Mv.cp_exAt _ _ _ t.exAt
      inGeo := Mv.cp_inGeo _ _ _ t.inGeo
      grpAt := grpAt_up S' N h t.grpAt
      grp := t.grp
      mu := muIsW_up S' N h t.mu
      exact := (@Eq.trans (Set (@Rows.Places.Pl B.LL B.instLL B.places)) Wt (@Dat.W1 (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w Z))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@RowsT.exact B f T K w Z Wt p0 t) (@Eq.symm (Set (@Rows.Places.Pl (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.LL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.instLL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.places)) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) eW1))
      untw := (t.untw)
      emt0 := (t.emt0)
      emt := (t.emt)
      etaF := t.etaF
      rowInt := rowInt_up S' N h t.rowInt
      idx := fun Y hY => idxDefs_up (Z := Z) (S' := S') (N := N) (h := h) Y
        (t.idx (divBack Y) (_root_.GlobalTheory.Mem.R3.Rw.Up.mjAre_back K B f T w Z t.hX Wt p0 t.r S' N h r' rfl h13 Y hY)) }
  have hs : RowsSame t t' :=
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, (HEq.refl t.r.z.cG), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  refine ⟨t', hs, (by with_unfolding_all exact ((HEq.refl (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo)) :)), ?_, _root_.GlobalTheory.Mem.R3.Rw.Up.rxs_up K B f T w Z Wt p0 t S' N h t' hs⟩
  exact (by with_unfolding_all exact ((congrArg (fun e => ({ (SRe.pkOf t).up Z S' N h with eE := e } : SRe.RowPk (SRe.upL Z S' N h).D)) (eq_of_heq h8)) :))

theorem rows_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := fun K B f T w Z Wt p0 t S' N h =>
  Exists.elim (rows_up_at K B f T w Z Wt p0 t S' N h) fun t' ht' =>
    ⟨Tr.baseLevelRowSideTransport (refUp Z S' N h) p0, t', ht'⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcFramedPointExtendsToModelBoundaryStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_framed_point_extends_to_model_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  first | exact @GlobalTheory.CuspFrom.arc_bdExt | exact GlobalTheory.CuspFrom.arc_bdExt | (intros; apply GlobalTheory.CuspFrom.arc_bdExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcsOnFlowLinesOfAnalyticModelOnOrbitStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  first | exact @GlobalTheory.CuspFrom.flowTie_of_onOrbit | exact GlobalTheory.CuspFrom.flowTie_of_onOrbit | (intros; apply GlobalTheory.CuspFrom.flowTie_of_onOrbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open scoped CommRingCat.HomTopology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc.Leave

theorem block_of_span_le {N p : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (h : Submodule.span ℂ (col M' '' {a | (a : ℕ) < p}) ≤ Submodule.span ℂ (col M '' {a | (a : ℕ) < p}))
    (a b : Fin N) (ha : p ≤ a) (hb : (b : ℕ) < p) : (M⁻¹ * M') a b = 0 := by
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj a).comp (Matrix.mulVecLin M⁻¹)
  have hL : ∀ (P : Matrix (Fin N) (Fin N) ℂ) (d : Fin N), L (col P d) = (M⁻¹ * P) a d := fun _ _ => rfl
  have h1 : Submodule.span ℂ (col M '' {a | (a : ℕ) < p}) ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    show L (col M d) = 0
    rw [hL, Matrix.nonsing_inv_mul _ hM.isUnit]
    exact Matrix.one_apply_ne fun e => absurd (show (d : ℕ) < p from hd) (by rw [← e]; omega)
  exact (hL M' b).symm.trans (h1 (h (Submodule.subset_span ⟨b, hb, rfl⟩)))

theorem imTop_neBot : imTop.NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem ht
    exact ⟨a * Complex.I, by simpa using ha⟩

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun w : ℂ => Real.exp (-(2 * Real.pi * w.im))) imTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (by positivity) tendsto_comap)
  refine h.congr fun w => ?_
  simp [eTwoPi, Complex.norm_exp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N}

theorem x_eq_of_samePos (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x x' : (U.X k).dom)
    (h : SamePos (U.X k) x.1 x'.1) : (U.un k x).x = (U.un k x').x :=
  GlobalTheory.TrueCx.PointWell.pt_eq_of_block (U := Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x x'
    (fun τ => block_of_span_le (x.2 τ).1 (h τ).ge) fun τ => block_of_span_le (x'.2 τ).1 (h τ).le

theorem isHolTo_ptC (hU : IsUnf U) (k : U.Comp) (s : Frame (U.X k).Ψ N → (U.X k).dom)
    (hs : ∀ x ∈ (U.X k).dom, (s x).1 = x) : IsHolTo (U.X k).dom fun x => GlobalTheory.TrueCx.ptC (U.un k (s x)) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  let L : Frame (U.X k).Ψ N ≃L[ℂ] (Fin (Module.finrank ℂ (Frame (U.X k).Ψ N)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
  have ho : IsOpen (U.X k).dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _
  have hB := ho.preimage L.symm.continuous
  have h1 := (F.hol (ik k) _ _ (fun b => P (s (L.symm b))) hB ⟨fun b _ => hP' _, fun a =>
    differentiableOn_pi.2 fun i => by
      simp only [hP]
      refine GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr _ (fun b _ => (s _).2) (fun τ a d => ?_) _ _ _
      refine (differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 L.symm.differentiable τ) a)
        d).differentiableOn.congr fun b hb => ?_
      rw [hs _ hb]
      rfl⟩).1
  have h2 : IsHolTo (L.symm ⁻¹' (U.X k).dom) fun b => GlobalTheory.TrueCx.ptC (U.un k (s (L.symm b))) := by
    refine GlobalTheory.TrueCx.TorHolo.isHolTo_of_fst _ _ hB _ (fun b => GlobalTheory.TrueCx.ptC_snd _) ?_
    simp only [GlobalTheory.TrueCx.ptC_fst]
    exact LocLift.isHolTo_congr h1 fun b _ => hx _
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h2 ho L.differentiableOn fun v hv => ?_) fun v _ => ?_
  · rwa [Set.mem_preimage, L.symm_apply_apply]
  · rw [L.symm_apply_apply]

theorem lift_not_converges : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T xx hσ hU ⟨⟨⟨hr, hψ⟩, hxs, hφ⟩, hb0, _⟩ hm hl x₀ hx₀ x' ht hev
  have := isProper_genStr Z
  have := imTop_neBot
  let s : Frame (U.X k).Ψ N → (U.X k).dom := fun v => if h : v ∈ (U.X k).dom then ⟨v, h⟩ else ⟨x₀, hx₀⟩
  have hs : ∀ v (h : v ∈ (U.X k).dom), s v = ⟨v, h⟩ := fun v h => dif_pos h
  let pt : Frame (U.X k).Ψ N → CxPts (genStr Z) σ := fun v =>
    ⟨GlobalTheory.TrueCx.ptC (U.un k (s v)) ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over, GlobalTheory.TrueCx.ptC_snd]⟩
  have hc : ContinuousOn pt (U.X k).dom := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo
    (LocLift.isHolTo_comp_hom (isHolTo_ptC hU k s fun v h => by rw [hs v h]) Z.jQ)
  have h1 : Tendsto (fun w => pt (x' w)) imTop (𝓝 (pt x₀)) :=
    (hc.continuousAt ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _).mem_nhds hx₀)).tendsto.comp ht
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  let q : CxPts (genStr Z) σ := ⟨spMap (ψ 0) ≫ x, by
    rw [Category.assoc, hxs, ← hφ 0 h0, ← Spec.map_comp]; rfl⟩
  have ha : ContinuousAt (fun u => spMap (ψ u) ≫ x) 0 := by
    refine ((GlobalTheory.Points.continuous_comp x).comp
      (GlobalTheory.Points.continuous_specMap (C := ℂ) (CommRingCat.of A))).continuousAt.comp
      (f := fun u => CommRingCat.ofHom (ψ u)) ?_
    refine (CommRingCat.HomTopology.isEmbedding_hom _ _).isInducing.continuousAt_iff.2 (continuousAt_pi.2 fun a => ?_)
    exact ((hψ a).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).continuousAt
  have h2 : Tendsto (fun w => pt (x' w)) imTop (𝓝 q) := by
    refine tendsto_subtype_rng.2 ((ha.tendsto.comp tendsto_eTwoPi).congr' ?_)
    filter_upwards [hev, tendsto_eTwoPi.eventually (Metric.isOpen_ball.mem_nhds h0),
      (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop T)] with w hw hb hT
    obtain ⟨hd, he, -⟩ := hl w hT
    have e1 := (hm _ hb (Complex.exp_ne_zero _)).1
    have e2 : GlobalTheory.TrueCx.ptC (U.un k (s (x' w))) = GlobalTheory.TrueCx.ptC (y (eTwoPi w)) := by
      refine pullback.hom_ext ?_ ((GlobalTheory.TrueCx.ptC_snd _).trans (GlobalTheory.TrueCx.ptC_snd _).symm)
      rw [GlobalTheory.TrueCx.ptC_fst, GlobalTheory.TrueCx.ptC_fst, hs _ hw.1]
      exact (x_eq_of_samePos hσ hU k ⟨_, hd⟩ ⟨_, hw.1⟩ hw.2).symm.trans he
    exact e1.symm.trans (congrArg (· ≫ Z.jQ) e2.symm)
  have h3 : (pt x₀).1 = q.1 := congrArg Subtype.val (tendsto_nhds_unique h1 h2)
  refine mem_genBd.1 (hb0 (IsLocalRing.closedPoint ℂ)) ⟨GlobalTheory.TrueCx.ptC (U.un k (s x₀)) (IsLocalRing.closedPoint ℂ), ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun f : Sp ℂ ⟶ gen Z => f (IsLocalRing.closedPoint ℂ)) h3)

end GlobalTheory.ShFam.BdArc.Leave
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  [Algebra c.F K]

theorem exists_genPt (Z : Model Xo c β) (φ : c.F →+* V) (hφ : (algebraMap V K).comp φ = algebraMap c.F K)
    (y : FrPt Xo c K) : ∃ χ : Sp V ⟶ gen Z, χ ≫ genStr Z = spMap φ ∧ GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap φ) (GlobalTheory.AllWt.ptF y ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp, hφ]
    exact pullback.lift_snd _ _ _)
  exact ⟨χ, h2, h1.symm⟩

theorem exists_genIdent (Z : Model Xo c β) {χ : Sp V ⟶ gen Z} {y : FrPt Xo c K}
    (hχ : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)) {t : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap V K))) (mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) (GlobalTheory.AllWt.ptF y)
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) (GlobalTheory.AllWt.ptF y) Z.m mF
  have hj : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap V K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F}

theorem mem_genBd_of_mem_genBd {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'}
    {t t' : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) (m' : SABMap t' Z'.t (χ' ≫ genι Z'))
    (ψ : SABMap t t' (𝟙 (Sp V))) (p : Sp V) (h : χ' p ∈ genBd Z') : χ p ∈ genBd Z := by
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z.t.semi m.cart.1 p]
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z'.t.semi m'.cart.1 p] at h
  have e := abLocus_pullback abLocusOne t'.semi ψ.cart.1 p
  have e0 : (𝟙 (Sp V)) p = p := rfl
  rw [e0] at e
  exact fun hp => h (e.2 hp)

section Chain

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {x : Sp V ⟶ Z.X} {x' : Sp V ⟶ Z'.X} {t t' : SAB H (Sp V)}
  (m : SABMap t Z.t x) (m' : SABMap t' Z'.t x') (ψ : SABMap t t' (𝟙 (Sp V))) {φ : c.F →+* V}

theorem exists_isEigBasis_chain {τ : E →+* ℂ} {n : ℕ} {v' : Fin n → (Sp (DualNumber V) ⟶ Z'.t.G.left)}
    (h : IsEigBasis Z'.t φ x' τ v') : ∃ v : Fin n → (Sp (DualNumber V) ⟶ t.G.left),
      (∀ i, (v i ≫ ψ.φ) ≫ m'.φ = v' i) ∧ (∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) ∧
        IsEigBasis Z.t φ x τ (fun i => v i ≫ m.φ) := by
  have h1 : IsEigBasis Z'.t φ (𝟙 _ ≫ x') τ v' := by rwa [Category.id_comp]
  obtain ⟨v₁, hv₁, h₁⟩ := isEigBasis_pull m' h1
  have h2 : IsEigBasis t' φ (𝟙 _ ≫ 𝟙 _) τ v₁ := by rwa [Category.id_comp]
  obtain ⟨v₂, hv₂, h₂⟩ := isEigBasis_pull ψ h2
  refine ⟨v₂, fun i => by rw [hv₂, hv₁], fun i => by rw [(h₂.1 i).1, Category.comp_id], ?_⟩
  have := isEigBasis_push m h₂
  rwa [Category.id_comp] at this

end Chain

section Frame

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'} {y : FrPt Xo c K}
  {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)} {t t' : SAB H (Sp V)}
  {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Z'.t (χ' ≫ genι Z')} {ψ : SABMap t t' (𝟙 (Sp V))}
  {a : SABMap tK t (spMap (algebraMap V K))} {a' : SABMap tK t' (spMap (algebraMap V K))}
  {mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)} {mF' : SABMap tK Z'.oF.t (GlobalTheory.AllWt.ptF y)}

theorem exists_lift_frameVec (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Z'.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Z'.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber V) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    {u' : Sp (DualNumber K) ⟶ Xo.univ.t.G.left} (hu' : u' ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ y.x)
    {w' : Sp (DualNumber K) ⟶ Z'.oF.t.G.left}
    (hw1 : w' ≫ Z'.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y)
    (hw2 : w' ≫ Z'.m0.toSABMap.φ = u') (hw3 : w' ≫ Z'.m.φ = spMap (dualMap (algebraMap V K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = u' ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ v ≫ m.φ := by
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  obtain ⟨u, hu1, hu2⟩ := exists_lift mK (spMap (algebraMap K (DualNumber K))) u' (by rw [hu', ← hx])
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) =
      spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp, PullbackSections.dualMap_comp_alg]
  have e1 : u ≫ mF'.φ = w' := by
    apply Z'.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hF0', hu2, hw2]
    · rw [Category.assoc, mF'.cart.1.w, ← Category.assoc, hu1, hw1]
  have e2 : u ≫ a.φ = spMap (dualMap (algebraMap V K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3]
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  refine ⟨u ≫ mF.φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  · rw [Category.assoc, hF0, hu2]
  · rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]

end Frame

theorem bdExt_of_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z O' _ β' Z' V K _ _ _ _ _ _ _ φ y hφ h
  obtain ⟨χ', g', e1', e2', hw', hb'⟩ := h
  obtain ⟨χ, e1, e2⟩ := exists_genPt Z φ hφ y
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ' ≫ genι Z') Z'.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_genIdent Z e2 mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_genIdent Z' e2' mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map V K t t' tK a a'
  choose v hv1 hv2 hv3 using fun τ => exists_isEigBasis_chain m m' ψ (EigFrame.isEigBasis g' τ)
  refine ⟨χ, eigFrameOf (fun τ i => v τ i ≫ m.φ) hv3, e1, e2, fun τ i => ?_,
    mem_genBd_of_mem_genBd m m' ψ _ hb'⟩
  let w' := Classical.choose (hw' τ i)
  have hw1 := (Classical.choose_spec (hw' τ i)).1
  have hw2 := (Classical.choose_spec (hw' τ i)).2.1
  have hw3 := (Classical.choose_spec (hw' τ i)).2.2
  have hw3' : w' ≫ Z'.m.φ = spMap (dualMap (algebraMap V K)) ≫ (v τ i ≫ ψ.φ) ≫ m'.φ :=
    hw3.trans (congrArg (fun z => spMap (dualMap (algebraMap V K)) ≫ z) (hv1 τ i).symm)
  exact exists_lift_frameVec hψ hF0 hFm hF0' hFm' (hv2 τ i) (y.tan τ i).1 hw1 hw2 hw3'

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
section
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.PeriodFrame

open GlobalTheory.ShFam.Hor

def combMat {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k i => ∑ m, (ε i m : ℂ) * l m k

def perTau {n g r₀ r : ℕ} (a : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ)
    (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ) (s : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (D : ℂ) • ((combMat (ζ (logExp a s)) α)⁻¹ * combMat (lam s) φ)

theorem combMat_comb {g r r' : ℕ} (w : Fin r' → Fin g → ℂ) (l : Fin r → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ)
    (α : Matrix (Fin g) (Fin r') ℚ) (hw : ∀ i, w i = ∑ j, c i j • l j) :
    combMat w α = combMat l (α * c.map (Int.cast : ℤ → ℚ)) := by
  ext k i
  simp only [combMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hw, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by
    simp only [Pi.mul_apply, Pi.intCast_apply]; ring

theorem combMat_add_mul {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (φ + bᵀ * ε) = combMat l φ + combMat l ε * b.map (Rat.cast : ℚ → ℂ) := by
  ext k j
  simp only [combMat, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem combMat_shift {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) (D : ℕ) (Bk : Matrix (Fin g) (Fin g) ℤ) (hP : IsUnit (combMat l ε).det)
    (hB : ∀ i j, (Bk i j : ℚ) = D * b i j) :
    (D : ℂ) • ((combMat l ε)⁻¹ * combMat l (φ + bᵀ * ε)) =
      (D : ℂ) • ((combMat l ε)⁻¹ * combMat l φ) + Bk.map (Int.cast : ℤ → ℂ) := by
  rw [combMat_add_mul, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, smul_add]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h := congrArg (Rat.cast : ℚ → ℂ) (hB i j)
  push_cast at h
  rw [h]

theorem shift_mem {n a : ℕ} (ha : a ≤ n) (k : Fin a) {s : Fin n → ℂ} (hs : s ∈ logDom n a) :
    s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I) ∈ logDom n a ∧
      logExp a (s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) = logExp a s := by
  simp only [logDom, Set.mem_setOf_eq] at hs ⊢
  constructor
  · intro j
    have h := hs j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [hk, if_true] at h ⊢
      simpa [Pi.add_apply] using h
    · simpa [Pi.add_apply, Pi.single_eq_of_ne hj] using h
  · funext j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, _root_.mul_one]
    · simp [logExp, Pi.single_eq_of_ne hj]

end GlobalTheory.PeriodFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexArcOfAnalyticModelOnFlowOrbitStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  first | exact @GlobalTheory.CuspFrom.exists_arcIn_input | exact GlobalTheory.CuspFrom.exists_arcIn_input | (intros; apply GlobalTheory.CuspFrom.exists_arcIn_input <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariantStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_core_constants_base_solution_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (cc : ∀ i : Fin D.R.m, (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (cc i) 1) → ∃ cE, (∀ i : Fin D.R.m, cE ((i : ℕ) + 1) T.σ₀ = cc i) ∧ TieIn (setCE T cE) R κ v₀ ∧ (∀ i, OMPins (setCE T cE) R κ v₀ O i) ∧ Fired (setCE T cE) R κ v₀ O (fun _ => 1) := by
  first | exact @GlobalTheory.RealGeoConst.exists_constants | exact GlobalTheory.RealGeoConst.exists_constants | (intros; apply GlobalTheory.RealGeoConst.exists_constants <;> assumption)
end

