module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0264
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0259
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0261
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompare
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0244
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGeometricHeightConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopNine

theorem nineGeoU_of_given (hG : Top.Given) (hW : Out.WeilSt) (hF : Fl.FlatDegree) :
    ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  obtain ⟨Ch, hCh⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.TopHt.htU_of_given hG hF
  obtain ⟨Cu, hCu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.top_mean_cusp_weight hG
  refine ⟨Ch, Cu, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT
  exact ⟨_root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_lower hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hT,
    hCh E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT,
    hCu E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U hII hAdm hU⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopNine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem given_of_inputs : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → Top.Given :=
  fun hModel hKey hSAH hSegre hResK hFar hGaga hLLD hPB hHS hAn hNine =>
    ⟨hModel, hKey, hSAH, hSegre, hResK, _root_.GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds, hFar, hGaga, (_root_.GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel hLLD).1, hPB, hHS, hAn, hNine,
      GlobalTheory.T.antisymmetric_perturbation_holds⟩

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareSecond
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.JoinPts

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {g : MRing ι} (h : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := (RingHom.mem_ker).1 h
  have e : ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ).comp (mConeMap y) =
      aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem aeval_map_hom {Ω' : Type} [Field Ω'] (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (fun p => i (y p)) g = i (aeval y g) := by
  have e : (aeval (fun p => i (y p)) : MRing ι →ₐ[ℤ] Ω') = (i.toIntAlgHom).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  rw [e]
  rfl

theorem cross_mem (y : (Σ k, ι k) → Ω) (p q p' q' : Σ k, ι k) (hp : p'.1 = p.1) (hq : q'.1 = q.1)
    (h : y p * y q' = y p' * y q) :
    (X p * X q' - X p' * X q : MRing ι) ∈ mCoordIdeal y := by
  refine (RingHom.mem_ker).2 ?_
  have e : (C (y p) * C (y q') : MvPolynomial K Ω) = C (y p') * C (y q) := by
    rw [← C_mul, ← C_mul, h]
  have hx : mConeMap y (X p * X q' - X p' * X q : MRing ι) =
      C (y p) * X p.1 * (C (y q') * X q'.1) - C (y p') * X p'.1 * (C (y q) * X q.1) := by
    simp [mConeMap]
  rw [hx, hp, hq]
  linear_combination (X p.1 * X q.1) * e

theorem exists_smul_of_cross {κ : Type} {u v : κ → ℂ} (hv : v ≠ 0) (h : ∀ a b, u a * v b = u b * v a) :
    ∃ t : ℂ, u = t • v := by
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hv
  have hb' : v b ≠ 0 := hb
  refine ⟨u b / v b, funext fun a => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  exact h a b

end Forms

theorem coordsAt_smul {X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X'} {K : Type}
    {ι : K → Type} {y : (Σ k, ι k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {w : (Σ k, ι k) → ℂ}
    (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := h.1 k
    exact ⟨a, (isUnit_iff_ne_zero.2 (hc k)).mul ha⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul ha.ne_zero)
    obtain ⟨hy, hr⟩ := h.2 k a ha'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, h1, h2⟩ := hr i
    refine ⟨r, h1, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, a⟩)
    rw [h2]
    ring

section Origin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {M : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

theorem mono_coeff (c : Coeff l) : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  have := IsPreimmersion.of_isLocalization (S := c.F) (nonZeroDivisors (𝓞 c.F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F))))

theorem exists_form (o : RootOrigin Y S M Fx) :
    ∃ b : MRing M.ι, aeval M.y b ≠ 0 ∧ ∀ w ∈ mcPts M.P, aeval w b ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X, CoordsAt o.𝔐.ξ M.y z w ∧ o.𝔐.Interior z := by
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 hinj
  obtain ⟨b, d, hd, hb, hw⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 x hx (mono_coeff c)
  refine ⟨b, fun h => hb (Small.LineModel.mem_of_aeval M.y hd h), fun w hw' hne => hw w hw' ?_⟩
  rw [Cmp.evC, Small.LineModel.eval_map_eq]
  exact hne

theorem exists_lift (o : RootOrigin Y S M Fx) (hJ : o.Re.J = ⊤) {w : (Σ k, M.ι k) → ℂ} (hw : w ∈ mcPts M.P)
    {z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X} (hz : CoordsAt o.𝔐.ξ M.y z w) (hI : o.𝔐.Interior z) :
    ∃ x : o.Re.R.X, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w ∧ o.Re.π x ∈ Sys.open' ∧
      ∃ t : ℂ, Fx.pt (o.Re.π x) = t • fun a => w ⟨o.k₀, o.ix a⟩ := by
  have hnot : w ∉ mcPts o.Re.J := by
    rw [hJ]
    intro h
    have := h.2 1 Submodule.mem_top
    simp at this
  obtain ⟨x, hx⟩ := o.Re.R.surj w hw hnot
  obtain ⟨k, hk, hxw⟩ := id hx
  refine ⟨x, hx, ?_, ?_⟩
  · have hC : CoordsAt o.𝔐.ξ M.y z (o.Re.R.lift x x) := by
      rw [hxw]
      exact coordsAt_smul hz hk
    exact (o.interior x z hC).1 hI
  · obtain ⟨α, hα, h⟩ := TowerOriginModel.pi_pt_ne o x
    refine ⟨α⁻¹ * k o.k₀, funext fun a => ?_⟩
    have h1 := congrFun h a
    rw [hxw] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_assoc, h1, inv_mul_cancel_left₀ hα]

end Origin

theorem join_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → o.Re.J = ⊤ → o₀.Re.J = ⊤ → ∃ f : MRing (Cmp.joinIdx M.ι R.ι), f ∉ mCoordIdeal (Ht.joinOf M R i) ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∃ (x : o.Re.R.X) (x' : o₀.Re.R.X) (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X), ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.Re.π x = o₀.Re.π x' ∧ o.Re.π x ∈ Sys.open' ∧ CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.𝔐.Interior z₁ ∧ o₀.𝔐.Interior z₂ := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  classical
  obtain ⟨b, hb, hbw⟩ := exists_form o
  obtain ⟨b₀, hb₀, hbw₀⟩ := exists_form o₀
  have eL : (Ht.joinOf M R i) ∘ Cmp.joinInl M.ι R.ι = M.y := rfl
  have eR : (Ht.joinOf M R i) ∘ Cmp.joinInr M.ι R.ι = fun p => i (R.y p) := rfl
  refine ⟨rename (Cmp.joinInl M.ι R.ι) b * rename (Cmp.joinInr M.ι R.ι) b₀, fun h => ?_, fun w hw hf => ?_⟩
  · have h0 := aeval_eq_zero_of_mem _ h
    rw [map_mul, aeval_rename, aeval_rename, eL, eR, aeval_map_hom] at h0
    exact (mul_ne_zero hb ((map_ne_zero i).2 hb₀)) h0
  · obtain ⟨hw₁, hw₂⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at hw₁ hw₂
    rw [Cmp.evC, Small.LineModel.eval_map_eq, map_mul, aeval_rename, aeval_rename] at hf
    obtain ⟨z₁, hz₁, hI₁⟩ := hbw _ hw₁ (left_ne_zero_of_mul hf)
    obtain ⟨z₂, hz₂, hI₂⟩ := hbw₀ _ hw₂ (right_ne_zero_of_mul hf)
    obtain ⟨x, hx, hxo, t, ht⟩ := exists_lift o hJ hw₁ hz₁ hI₁
    obtain ⟨x', hx', -, t', ht'⟩ := exists_lift o₀ hJ₀ hw₂ hz₂ hI₂
    refine ⟨x, x', z₁, z₂, hx, hx', ?_, hxo, hz₁, hz₂, hI₁, hI₂⟩
    have hcross : ∀ a b', w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) =
        w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) := by
      intro a b'
      have hm := cross_mem (Ht.joinOf M R i) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) rfl rfl (by
          show M.y _ * i (R.y _) = M.y _ * i (R.y _)
          have hg : ∀ u, i (o₀.g u) = o.g u := fun u => congrArg (fun φ : Fx.Ωf →+* M.Ω => φ u) hi
          rw [o.y_eq, o.y_eq, o₀.y_eq, o₀.y_eq, hg, hg]
          ring)
      have h0 := hw.2 _ hm
      simp only [map_sub, map_mul, aeval_X] at h0
      exact sub_eq_zero.1 h0
    obtain ⟨s, hs⟩ := exists_smul_of_cross (u := Fx.pt (o.Re.π x)) (v := Fx.pt (o₀.Re.π x')) (Fx.pt_ne _)
      (fun a b' => by
        rw [ht, ht']
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (t * t') * hcross a b')
    exact Fx.pt_inj _ _ s hs

end GlobalTheory.CompanionTheory.Ar.JoinPts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareThird
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.ALine

section Cross

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Cmp

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω]

theorem cross_mem (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) :
    (X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) +
        -(X (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) : MRing (joinIdx ι₁ ι₂)) ∈
      mCoordIdeal (joinVec y₁ y₂) := by
  classical
  have hl : ∀ a : ι₁ k₁, IsMultiHomog (X (joinInl ι₁ ι₂ ⟨k₁, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inl k₁) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a
  have hr : ∀ a : ι₂ k₂, IsMultiHomog (X (joinInr ι₁ ι₂ ⟨k₂, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inr k₂) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a
  refine Small.LineModel.mem_of_aeval _
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhAdd (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl a₁) (hr b₂))
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhNeg (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl b₁) (hr a₂)))) ?_
  simp only [map_add (f := _), map_neg, map_mul, aeval_X]
  show y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ + -(y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) = 0
  rw [h]; ring

theorem cross_eq (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) =
      z (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) := by
  have h0 := hz.2 _ (cross_mem y₁ y₂ a₁ b₁ a₂ b₂ h)
  simp only [map_add (f := _), map_neg, map_mul, aeval_X] at h0
  linear_combination h0

theorem hasVal_one (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ : ι₁ k₁) (a₂ : ι₂ k₂) (h : y₁ ⟨k₁, a₁⟩ = y₂ ⟨k₂, a₂⟩)
    (d : K₁ ⊕ K₂ → ℤ) (hd₁ : d (Sum.inl k₁) = 1) (hd₂ : d (Sum.inr k₂) = -1)
    (hd : ∀ k, k ≠ Sum.inl k₁ → k ≠ Sum.inr k₂ → d k = 0)
    {L : Type} [Field L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L)
    (hz : z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) ≠ 0) :
    Small.HasVal (joinVec y₁ y₂) d 1 z
      (z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) / z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) := by
  classical
  refine ⟨Pi.single (Sum.inl k₁) 1, Pi.single (Sum.inr k₂) 1, X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩),
    X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩), ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a₁,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a₂, fun k => ?_, ?_, ?_, ?_⟩
  · by_cases e₁ : k = Sum.inl k₁
    · subst e₁; simp [hd₁]
    · by_cases e₂ : k = Sum.inr k₂
      · subst e₂; simp [hd₂]
      · simp [hd k e₁ e₂, e₁, e₂]
  · simp only [aeval_X, one_mul]
    exact h
  · simpa only [aeval_X] using hz
  · simp only [aeval_X]
    field_simp

end Cross

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), ∀ v : ℂ, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 w v → M.A.h (fun p => w (Cmp.joinInl M.ι R.ι p)) = ‖v‖ * R.A.h (fun p => w (Cmp.joinInr M.ι R.ι p)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi
  classical
  have hy : ∀ a, M.y ⟨o.k₀, o.ix a⟩ = i (R.y ⟨o₀.k₀, o₀.ix a⟩) := fun a => by
    rw [o.y_eq, o₀.y_eq, ← hi]; rfl
  have hd₁ : Ht.joinDeg M R none (Sum.inl o.k₀) = 1 := o.A_deg.1
  have hd₂ : Ht.joinDeg M R none (Sum.inr o₀.k₀) = -1 := by
    show -(R.A.a o₀.k₀) = -1
    rw [o₀.A_deg.1]
  have hd : ∀ k, k ≠ Sum.inl o.k₀ → k ≠ Sum.inr o₀.k₀ → Ht.joinDeg M R none k = 0 := by
    rintro (k | k) h₁ h₂
    · exact o.A_deg.2 k fun e => h₁ (congrArg _ e)
    · show -(R.A.a k) = 0
      rw [o₀.A_deg.2 k fun e => h₂ (congrArg _ e), neg_zero]
  have hval : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L) (a : Fin (Fx.m + 1)),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 →
      Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 z
        (z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) / z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩)) :=
    fun L _ z a hz => hasVal_one M.y (fun p => i (R.y p)) (o.ix a) (o₀.ix a) (hy a) _ hd₁ hd₂ hd z hz
  have hcr : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a b : Fin (Fx.m + 1),
      z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) =
        z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) :=
    fun L _ z hz a b => cross_eq M.y (fun p => i (R.y p)) (o.ix a) (o.ix b) (o₀.ix a) (o₀.ix b) (by
      show M.y _ * i (R.y _) = M.y _ * i (R.y _)
      rw [hy a, hy b, mul_comm]) hz
  have hexR : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inr o₀.k₀)
    have e : o₀.ix (o₀.ix.symm p) = p := o₀.ix.apply_symm_apply p
    exact ⟨o₀.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : R.ι o₀.k₀ => z ⟨Sum.inr o₀.k₀, x⟩) e.symm).trans h0)⟩
  have hexM : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inl o.k₀)
    have e : o.ix (o.ix.symm p) = p := o.ix.apply_symm_apply p
    exact ⟨o.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : M.ι o.k₀ => z ⟨Sum.inl o.k₀, x⟩) e.symm).trans h0)⟩
  have hne : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a : Fin (Fx.m + 1),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 → z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz a ha h0
    obtain ⟨b, hb⟩ := hexM L z hz
    have h1 := hcr L z hz b a
    rw [h0, zero_mul] at h1
    exact mul_ne_zero hb ha h1
  refine ⟨fun L _ _ z hz => ?_, fun w hw v hv => ?_⟩
  · obtain ⟨a, ha⟩ := hexR L z hz
    exact ⟨_, div_ne_zero (hne L z hz a ha) ha, hval L z a ha⟩
  · obtain ⟨a, ha⟩ := hexR ℂ w hw
    have hv' := Small.LineModel.hasVal_unique _ _ _ hw hv (hval ℂ w a ha)
    have hvne : v ≠ 0 := hv' ▸ div_ne_zero (hne ℂ w hw a ha) ha
    have hblock : ∀ b : Fin (Fx.m + 1), w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) =
        v * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) := by
      intro b
      rw [hv', div_mul_eq_mul_div, eq_div_iff ha]
      exact hcr ℂ w hw b a
    obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at h1 h2
    let c : R.K → ℂ := fun k => if k = o₀.k₀ then v else 1
    have hc : ∀ k, c k ≠ 0 := by
      intro k
      by_cases hk : k = o₀.k₀
      · simpa [c, hk] using hvne
      · simp [c, hk]
    have e1 := o.A_h _ h1
    have e2 := o₀.A_h _ (mcPts_smul R.arith.2.1.2.1 c hc h2)
    have e3 := R.A.smul c (fun p => w (Cmp.joinInr M.ι R.ι p)) hc
    have e4 : (∏ k, ‖c k‖ ^ R.A.a k) = ‖v‖ := by
      rw [Finset.prod_eq_single o₀.k₀]
      · simp [c, o₀.A_deg.1]
      · intro k _ hk
        simp [c, hk, o₀.A_deg.2 k hk]
      · simp
    rw [e1, ← e4, ← e3, e2]
    congr 1
    funext b
    simpa [c] using hblock b

end GlobalTheory.CompanionTheory.Ar.Ht.ALine
end
end

